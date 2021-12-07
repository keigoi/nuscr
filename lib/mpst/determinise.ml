open! Base
open Err
open Names
open! Ltype

type add_state_env =
  { current: TypeVariableName.t option
  ; namegen: Namegen.t
  ; rename: string Map.M(TypeVariableName).t
  ; binding: Gtype.t Lazy.t Map.M(TypeVariableName).t }

let new_add_state_env =
  { current= None
  ; namegen= Namegen.create ()
  ; rename= Map.empty (module TypeVariableName)
  ; binding= Map.empty (module TypeVariableName) }

(* add each 'state' a mu binder. *)
let rec normalise_stateful' (env : add_state_env) (g_type : Gtype.t) =
  let open Gtype in
  let env, maybe_mu =
    if Option.is_none env.current then
      let namegen, tv = Namegen.unique_name env.namegen "state" in
      ( {env with namegen}
      , fun t -> MuG (TypeVariableName.of_string tv, [], t) )
    else (env, fun t -> t)
  in
  match g_type with
  | MessageG (m, send_r, recv_r, g_type) ->
      let env, g_type =
        normalise_stateful' {env with current= None} g_type
      in
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
           normalise_stateful'
             {namegen; rename; binding; current= Some tv}
             g_type )
      in
      let env, g_type = Lazy.force env__g_type in
      (env, MuG (TypeVariableName.of_string tv', rec_vars, g_type))
  | ChoiceG (r, g_types) ->
      let env, g_types =
        List.fold_left ~init:(env, [])
          ~f:(fun (env, g_types) g_type ->
            let env, g_type =
              normalise_stateful' {env with current= None} g_type
            in
            (env, g_type :: g_types) )
          g_types
      in
      (env, maybe_mu (ChoiceG (r, List.rev g_types)))
  | TVarG (tv, expr, _) ->
      let self = Map.find_exn env.binding tv in
      let tv' = Map.find_exn env.rename tv in
      (env, TVarG (TypeVariableName.of_string tv', expr, self))
  | EndG -> (env, g_type)
  | CallG (_, _, _, _) -> assert false

let normalise_stateful g_type =
  snd @@ normalise_stateful' new_add_state_env g_type

(* unwind (remove) mu binders of a global type. *)
module TypeVariableNameSet = struct
  type t = Set.M(TypeVariableName).t [@@deriving sexp_of]

  let compare = Set.compare_direct

  let singleton = Set.singleton (module TypeVariableName)

  let of_list = Set.of_list (module TypeVariableName)

  let union_list = Set.union_list (module TypeVariableName)

  let decode_prefix = "__states_"

  let decode_sep = '-'

  let decode (tv : TypeVariableName.t) =
    let tvstr = TypeVariableName.user tv in
    if String.is_substring_at ~pos:0 ~substring:decode_prefix tvstr then
      let tvstr = String.chop_prefix_exn tvstr ~prefix:decode_prefix in
      let tvars = String.split ~on:decode_sep tvstr in
      let tvars = List.map ~f:TypeVariableName.of_string tvars in
      of_list tvars
    else singleton tv

  let encode (tvars : t) =
    if Set.length tvars = 1 then Set.choose_exn tvars
    else
      let tvars = Set.to_list tvars in
      let tvars = List.map ~f:TypeVariableName.user tvars in
      let tvstr = String.concat ~sep:(String.of_char decode_sep) tvars in
      TypeVariableName.of_string (decode_prefix ^ tvstr)

  include Comparator.Make (struct
    type nonrec t = t

    let compare = compare

    let sexp_of_t = sexp_of_t
  end)
end

let rec unwind_gtype (g_type : Gtype.t) =
  let open Gtype in
  match g_type with
  | MessageG (_, _, _, _) -> ([], g_type)
  | ChoiceG (_, _) | EndG -> ([], g_type)
  | MuG (tv, _, g_type) ->
      let tvars, g_type = unwind_gtype g_type in
      (tv :: tvars, g_type)
  | TVarG (tv, _, self) ->
      let tvars, g_type = unwind_gtype (Lazy.force self) in
      (tv :: tvars, g_type)
  | CallG (_, _, _, _) -> assert false

let get_powerset_state = function
  | EndL -> None
  | MuL (tvar, _, _) -> Some (TypeVariableNameSet.decode tvar)
  | _ -> assert false

type project_env =
  { bound: Set.M(TypeVariableNameSet).t Lazy.t
  ; state_binding: t Lazy.t Map.M(TypeVariableNameSet).t }

let rec project_nondet' ~visited ~env (projected_role : RoleName.t)
    (g : Gtype.t) : (t list, TypeVariableName.t list) Either.t =
  let current = List.hd_exn visited in
  let is_visited tv = List.mem ~equal:TypeVariableName.equal visited tv in
  match g with
  | Gtype.EndG -> Either.First [EndL]
  | Gtype.MessageG (m, send_r, recv_r, g_type) ->
      (* standard projection *)
      if RoleName.equal projected_role send_r then
        Either.First
          [ MuL
              ( current
              , []
              , lazy (SendL (m, recv_r, project' ~env projected_role g_type))
              ) ]
      else if RoleName.equal projected_role recv_r then
        Either.First
          [ MuL
              ( current
              , []
              , lazy (RecvL (m, send_r, project' ~env projected_role g_type))
              ) ]
      else project_nondet' ~visited ~env projected_role g_type
  | Gtype.ChoiceG (choice_r, g_types)
    when RoleName.equal projected_role choice_r ->
      (* internal choice *)
      let ltys, epsilon =
        List.partition_map
          ~f:(project_nondet' ~visited ~env projected_role)
          g_types
      in
      let epsilon = List.concat epsilon in
      if List.length epsilon > 0 then
        (* self epsilon-loop is not acceptable *)
        violation "Internal choice has a self epsilon-loop"
      else
        let t =
          lazy
            (let ltys =
               List.concat_map ltys ~f:(function
                 | [MuL (_, _, (lazy (SendL (_, _, _) as lty)))] -> [lty]
                 | [MuL (_, _, (lazy (ChoiceL (_, ltys))))] ->
                     (* would this happen? (nested choices are already
                        flattened) *)
                     ltys
                 | [_] -> violation "internal choice has a non-output branch"
                 | _ ->
                     violation
                       "internal choice has a nondeterministic branch" )
             in
             ChoiceL (choice_r, ltys) )
        in
        Either.First [MuL (current, [], t)]
  | Gtype.ChoiceG (_, g_types) ->
      (* non-deterministic choice -- defer merging to eliminate backward
         epsilon transition *)
      let ltys, epsilon =
        List.partition_map
          ~f:(project_nondet' ~visited ~env projected_role)
          g_types
      in
      let epsilon = List.concat epsilon in
      let ltys = List.concat ltys in
      if List.length ltys > 0 then
        (* return only concrete (non-epsilon) transitions -- the ones beyond
           backward epsilons are counted at the caller's site. *)
        Either.First ltys (* multiple transitions *)
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
  | Gtype.MuG (tv, _, g_type) ->
      (* visited a recursion variable for the first time. unfold it. *)
      (* unfolding is implicit, as TVarG has its expanded form lazily in the
         3rd arg *)
      (* record tv so that we can detect backward links *)
      project_nondet' ~visited:(tv :: visited) ~env projected_role g_type
  | Gtype.TVarG (tv, _, _) when is_visited tv ->
      (* already visited this state i.e. this is a backward epsilon
         transition *)
      Either.Second [tv]
  | Gtype.TVarG (tv, _, self) ->
      (* a variable -- actually unfold it *)
      project_nondet' ~visited:(tv :: visited) ~env projected_role
        (Lazy.force self)
  | Gtype.CallG (_, _, _, _) -> (* TODO *) assert false

and project_nondet ~visited ~env projected_role g_type =
  match
    (* compute all transitions *)
    project_nondet' ~visited ~env projected_role g_type
  with
  | Either.First ts ->
      (* concrete transitions found *)
      ts
  | Either.Second _ ->
      (* there are only self epsilon-loops *)
      [EndL]

and merge_body ~env projected_role ltys =
  let rec aux (acc : (LabelName.t * t) list) = function
    | RecvL (m, _, lty) as l -> (
        let {Gtype.label; _} = m in
        match List.Assoc.find acc ~equal:LabelName.equal label with
        | None -> (label, l) :: acc
        | Some (RecvL (m_, r, l_))
          when List.equal Gtype.equal_payload m.Gtype.payload
                 m_.Gtype.payload ->
            (* input labels overlap. merge recursively *)
            List.Assoc.add acc ~equal:LabelName.equal label
              (RecvL (m, r, merge_stateful ~env projected_role [lty; l_]))
        | Some (RecvL _) -> violation "Payload type mismatch"
        | _ ->
            violation "Merge receive must be merging\n   receive local types"
        )
    | _ -> violation "Merge receive must be merging\n   receive local types"
  in
  match ltys with
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
          ltys
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
  | EndL :: ls when List.for_all ls ~f:(Ltype.equal EndL) -> EndL
  | [(SendL (_, _, _) as l)] -> l
  | [(ChoiceL (_, _) as l)] -> l
  | ts ->
      violation @@ "Can't merge.\n   projected role:"
      ^ RoleName.user projected_role
      ^ " protocol: \n"
      ^ String.concat ~sep:"\n\n and \n"
      @@ List.map ~f:show ts

and merge_stateful ~env projected_role ltys =
  if equal EndL (List.hd_exn ltys) then
    (* all branches must be end *)
    if List.for_all ~f:(equal EndL) ltys then EndL
    else violation "Can't merge. One of branches is an end."
  else
    (* split state ids *)
    let split_state_id = function
      | MuL (tv, _, lty) -> (TypeVariableNameSet.decode tv, lty)
      | TVarL (tv, _) ->
          let tvars = TypeVariableNameSet.decode tv in
          (tvars, Map.find_exn env.state_binding tvars)
      | _ -> assert false
    in
    let tvars, ltys = List.unzip @@ List.map ~f:split_state_id ltys in
    let state_id =
      (* and calculate the powerset state *)
      TypeVariableNameSet.union_list tvars
    in
    if Set.mem (Lazy.force env.bound) state_id then
      (* already bound *)
      TVarL (TypeVariableNameSet.encode state_id, [])
    else
      let bound =
        List.fold_left ~init:(Lazy.force env.bound) ~f:Set.remove tvars
      in
      let bound = Set.add bound state_id in
      let lty =
        lazy
          (merge_body
             ~env:{env with bound= Lazy.from_val bound}
             projected_role
             (List.map ~f:Lazy.force ltys) )
      in
      MuL (TypeVariableNameSet.encode state_id, [], lty)

and project' ~env projected_role (g_type : Gtype.t) : t =
  let tvars, g_type = unwind_gtype g_type in
  let rec env_with_current_state =
    (* mark current state as mu-bound *)
    { env with
      bound=
        lazy
          (let current_state = get_powerset_state (Lazy.force t)
           and bound = Lazy.force env.bound in
           Option.value_map ~f:(Set.add bound) current_state ~default:bound
          ) }
  and ltys =
    lazy
      (project_nondet ~visited:tvars ~env:env_with_current_state
         projected_role g_type )
  and t = lazy (merge_stateful ~env projected_role (Lazy.force ltys)) in
  let t =
    List.fold_left ~init:t
      ~f:(fun lty tvar -> lazy (MuL (tvar, [], lty)))
      (List.tl_exn tvars)
  in
  Lazy.force t

let project projected_role g_type =
  let env =
    { bound= Lazy.from_val @@ Set.empty (module TypeVariableNameSet)
    ; state_binding= Map.empty (module TypeVariableNameSet) }
  in
  let t = project' ~env projected_role (normalise_stateful g_type) in
  t
