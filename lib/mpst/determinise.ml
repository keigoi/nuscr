open! Base
open Gtype
open Err
open Names

type add_state_env =
  { current: TypeVariableName.t option
  ; namegen: Namegen.t
  ; rename: string Map.M(TypeVariableName).t
  ; binding: Gtype.t Lazy.t Map.M(TypeVariableName).t }

let rec add_states (env : add_state_env) (g_type : t) =
  let open Gtype in
  match g_type with
  | MessageG (m, send_r, recv_r, g_type) ->
      let env, maybe_mu =
        if Option.is_none env.current then
          let namegen, tv = Namegen.unique_name env.namegen "state" in
          ( {env with namegen}
          , fun t -> MuG (TypeVariableName.of_string tv, [], t) )
        else (env, fun t -> t)
      in
      let env, g_type = add_states env g_type in
      (env, maybe_mu @@ MessageG (m, send_r, recv_r, g_type))
  | MuG (tv, rec_vars, g_type) ->
      let namegen, tv' =
        Namegen.unique_name env.namegen (TypeVariableName.user tv)
      in
      let rename = Map.add_exn env.rename ~key:tv ~data:tv' in
      let rec env__g_type =
        lazy
          (let self = lazy (snd @@ Lazy.force env__g_type) in
           let binding = Map.add_exn env.binding ~key:tv ~data:self in
           add_states {namegen; rename; binding; current= Some tv} g_type )
      in
      let env, g_type = Lazy.force env__g_type in
      (env, MuG (TypeVariableName.of_string tv', rec_vars, g_type))
  | ChoiceG (r, g_types) ->
      let env, g_types =
        List.fold_left ~init:(env, [])
          ~f:(fun (env, g_types) g_type ->
            let env, g_type = add_states {env with current= None} g_type in
            (env, g_type :: g_types) )
          g_types
      in
      (env, ChoiceG (r, List.rev g_types))
  | TVarG (tv, expr, _) ->
      let self = Map.find_exn env.binding tv in
      let tv' = Map.find_exn env.rename tv in
      (env, TVarG (TypeVariableName.of_string tv', expr, self))
  | EndG -> (env, g_type)
  | CallG (_, _, _, _) -> assert false

let rec unwind (g_type : Gtype.t) =
  match g_type with
  | MessageG (_, _, _, _) -> ([], g_type)
  | ChoiceG (_, _) | EndG -> ([], g_type)
  | MuG (tv, _, g_type) ->
      let tvars, g_type = unwind g_type in
      (tv :: tvars, g_type)
  | TVarG (tv, _, self) ->
      let tvars, g_type = unwind (Lazy.force self) in
      (tv :: tvars, g_type)
  | CallG (_, _, _, _) -> assert false

type t =
  | RecvL of Gtype.message * RoleName.t * t Lazy.t
  | SendL of Gtype.message * RoleName.t * t Lazy.t
  | ChoiceL of RoleName.t * t list
  | TVarL of TypeVariableName.t * Expr.t list
  | MuL of TypeVariableName.t * (bool * Gtype.rec_var) list * t
  | EndL
[@@deriving sexp_of, eq]

let end_state = TypeVariableName.of_string "__end_state"

module TypeVariableNameSet = struct
  type t = Set.M(TypeVariableName).t [@@deriving sexp_of]

  let compare = Set.compare_direct

  let equal = Set.equal

  let singleton = Set.singleton (module TypeVariableName)

  let of_list = Set.of_list (module TypeVariableName)

  let union_list = Set.union_list (module TypeVariableName)

  include Comparator.Make (struct
    type nonrec t = t

    let compare = compare

    let sexp_of_t = sexp_of_t
  end)
end

let get_state_id = function
  | EndL -> None
  | MuL (_tvar, _, _) -> Some (assert false (*tvar*))
  | _ -> assert false

type project_env =
  { bound: Set.M(TypeVariableNameSet).t Lazy.t
  ; state_binding: t Lazy.t Map.M(TypeVariableNameSet).t }

let rec transitions ~visited ~env (projected_role : RoleName.t) (g : Gtype.t)
    : (t list, TypeVariableName.t list) Either.t =
  let current = List.hd_exn visited in
  let is_visited tv = List.mem ~equal:TypeVariableName.equal visited tv in
  match g with
  | EndG -> Either.First [EndL]
  | MuG (tv, _, g_type) ->
      (* visited a recursion variable for the first time. unfold it. *)
      (* unfolding is implicit, as TVarG has its expanded form lazily in the
         3rd arg *)
      (* record tv so that we can detect backward links *)
      transitions ~visited:(tv :: visited) ~env projected_role g_type
  | TVarG (tv, _, _) when is_visited tv ->
      (* already visited this state i.e. this is a backward epsilon
         transition *)
      Either.Second [tv]
  | TVarG (tv, _, self) ->
      (* a variable -- actually unfold it *)
      transitions ~visited:(tv :: visited) ~env projected_role
        (Lazy.force self)
  | MessageG (m, send_r, recv_r, g_type) ->
      if RoleName.equal projected_role send_r then
        Either.First
          [ MuL
              ( current
              , []
              , SendL (m, recv_r, lazy (project' ~env projected_role g_type))
              ) ]
      else if RoleName.equal projected_role recv_r then
        Either.First
          [ MuL
              ( current
              , []
              , RecvL (m, send_r, lazy (project' ~env projected_role g_type))
              ) ]
      else transitions ~visited ~env projected_role g_type
  | ChoiceG (choice_r, g_types) when RoleName.equal projected_role choice_r
    ->
      (* internal choice *)
      let trans, epsilon =
        List.partition_map
          ~f:(transitions ~visited ~env projected_role)
          g_types
      in
      let epsilon = List.concat epsilon in
      if List.length epsilon > 0 then
        (* no self epsilon-loop allowed *)
        violation "Internal choice has a self epsilon-loop"
      else
        let ltys =
          List.concat_map trans ~f:(function
            | [MuL (_, _, (SendL (_, _, _) as lty))] -> [lty]
            | [MuL (_, _, ChoiceL (_, ltys))] ->
                (* would this happen? (nested choices are already
                   flattened?) *)
                ltys
            | [_] -> violation "internal choice has a non-output branch"
            | _ -> violation "internal choice has a nondeterministic branch" )
        in
        Either.First [MuL (current, [], ChoiceL (choice_r, ltys))]
  | ChoiceG (_, g_types) ->
      (* non-deterministic choices *)
      let trans, epsilon =
        List.partition_map
          ~f:(transitions ~visited ~env projected_role)
          g_types
      in
      let epsilon = List.concat epsilon in
      let trans = List.concat trans in
      if List.length trans > 0 then
        (* return only concrete (non-epsilon) transitions -- the ones beyond
           backward epsilons are counted at the caller's site. *)
        Either.First trans (* multiple transitions *)
      else
        (* no conrete transitions -- check if there are backward epsilon
           links *)
        let epsilon =
          List.filter
            ~f:(fun tv ->
              not @@ List.mem ~equal:TypeVariableName.equal visited tv )
            epsilon
        in
        if List.length epsilon = 0 then
          (* no backward links (self loop only) -- end *)
          Either.First [EndL]
        else (* backward links *)
          Either.Second epsilon
  | CallG (_, _, _, _) -> (* TODO *) assert false

and merge_body ~env projected_role types : t =
  let rec aux (acc : (LabelName.t * t) list) = function
    | RecvL (m, _, lty) as l -> (
        let {label; _} = m in
        match List.Assoc.find acc ~equal:LabelName.equal label with
        | None -> (label, l) :: acc
        | Some (RecvL (m_, r, l_))
          when List.equal equal_payload m.Gtype.payload m_.Gtype.payload ->
            (* input labels overlap. merge recursively *)
            List.Assoc.add acc ~equal:LabelName.equal label
              (RecvL
                 ( m
                 , r
                 , lazy
                     (merge_state ~env projected_role
                        [Lazy.force lty; Lazy.force l_] ) ) )
        | Some (RecvL _) -> violation "Payload type mismatch"
        | _ ->
            violation "Merge receive must be merging\n   receive local types"
        )
    | _ -> violation "Merge receive must be merging\n   receive local types"
  in
  match types with
  | (RecvL (_, sender_r, _) :: _ | ChoiceL (sender_r, _) :: _)
    when not @@ RoleName.equal projected_role sender_r -> (
      let recvs =
        List.concat_map
          ~f:(function
            | RecvL (_, sender_r, _) as l -> [(sender_r, l)]
            | ChoiceL (sender_r, ls)
              when not @@ RoleName.equal projected_role sender_r ->
                List.map ~f:(fun l -> (sender_r, l)) ls
            | _t ->
                violation @@ "Merge should be receive local types: "
                (* ^ show t *) )
          types
      in
      let senders, recvs = List.unzip recvs in
      let sender =
        match senders with
        | [r] -> r
        | r :: rs when List.for_all ~f:(RoleName.equal r) rs -> r
        | _ -> violation "Merge sender must be identical"
      in
      let conts = List.fold ~f:aux ~init:[] recvs in
      match conts with
      | [] -> EndL
      | [(_, lty)] -> lty
      | conts -> ChoiceL (sender, List.map ~f:snd conts) )
  | EndL :: ls when List.for_all ls ~f:(equal EndL) -> EndL
  | [(SendL (_, _, _) as l)] -> l
  | [(ChoiceL (sender_r, _) as l)]
    when RoleName.equal projected_role sender_r ->
      l
  | _ (*ts*) ->
      violation @@ "Can't merge.\n   projected role:"
      ^ RoleName.user projected_role
      ^ " protocol: \n"

(* ^ String.concat ~sep:"\n\n and \n" @@ List.map ~f:show ts *)
and merge_state ~env projected_role ltys =
  if equal EndL (List.hd_exn ltys) then
    if List.for_all ~f:(equal EndL) ltys then EndL
    else violation "Can't merge. One of branches is an end."
  else
    let split_tyvar = function
      | MuL (tv, _, lty) -> ((assert false : TypeVariableNameSet.t), lty)
      | TVarL (tv, _) ->
          let tv = (assert false : TypeVariableNameSet.t) in
          (tv, Lazy.force @@ Map.find_exn env.state_binding tv)
      | _ -> assert false
    in
    let tvars, ltys = List.unzip @@ List.map ~f:split_tyvar ltys in
    let bound =
      List.fold_left ~init:(Lazy.force env.bound) ~f:Set.remove tvars
    in
    let bound = Set.add bound (assert false) (*tvars*) in
    let lty =
      merge_body
        ~env:{env with bound= Lazy.from_val bound}
        projected_role ltys
    in
    MuL (assert false (* tvars *), [], lty)

and project' ~env projected_role (g_type : Gtype.t) : t =
  let tvars, g_type = unwind g_type in
  let rec ltys =
    lazy
      ( match
          (* compute all transitions *)
          transitions ~visited:tvars
            ~env:(Lazy.force env_with_current_state)
            projected_role g_type
        with
      | Either.First ts -> ts
      | Either.Second _ -> [EndL] )
  and env_with_current_state =
    (* record current state as bound *)
    lazy
      (let bound0 = Lazy.force env.bound in
       { env with
         bound=
           lazy
             (Option.value_map
                (Lazy.force current_state)
                ~default:bound0 ~f:(Set.add bound0) ) } )
  and current_state = lazy (get_state_id (Lazy.force t))
  and t = lazy (merge_state ~env projected_role (Lazy.force ltys)) in
  let lty = MuL (assert false (*current_state*), [], Lazy.force t) in
  let lty =
    List.fold_left ~init:lty ~f:(fun lty tvar -> MuL (tvar, [], lty)) tvars
  in
  lty
