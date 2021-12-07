open! Base
open Printf
open Gtype
open Err
open Names
open Syntaxtree

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

type trans =
  | Out of (message * RoleName.t * Gtype.t) list
  | Inp of message * RoleName.t * Gtype.t
  | End

let end_state = TypeVariableName.of_string "__end_state"

let rec transitions ~visited (projected_role : RoleName.t) (g : Gtype.t) =
  let current = List.hd_exn visited in
  let is_visited tv = List.mem ~equal:TypeVariableName.equal visited tv in
  match g with
  | MessageG (m, send_r, recv_r, g_type) ->
      if RoleName.equal projected_role send_r then
        Either.First [(current, Out [(m, recv_r, g_type)])]
      else if RoleName.equal projected_role recv_r then
        Either.First [(current, Inp (m, send_r, g_type))]
      else transitions ~visited projected_role g_type
  | ChoiceG (choice_r, g_types) ->
      (* internal choice *)
      let trans, epsilon =
        List.partition_map ~f:(transitions ~visited projected_role) g_types
      in
      let epsilon = List.concat epsilon in
      if RoleName.equal projected_role choice_r then
        (* internal choice *)
        if List.length epsilon > 0 then
          violation "Internal choice has a self epsilon-loop"
        else
          let trans =
            List.concat_map trans ~f:(fun g_type ->
                match g_type with
                | [(_, Out trans)] -> trans
                | _ ->
                    violation
                      "internal choice has nondeterministic/non-output \
                       branch" )
          in
          Either.First [(current, Out trans)]
      else
        (* non-deterministic choices -- filter out backward epsilon
           transitions *)
        let trans = List.concat trans in
        if List.length trans > 0 then Either.First trans
        else
          let epsilon =
            List.filter
              ~f:(fun tv ->
                not @@ List.mem ~equal:TypeVariableName.equal visited tv )
              epsilon
          in
          if List.length epsilon = 0 then Either.First [(end_state, End)]
          else Either.second epsilon
  | EndG -> Either.First [(end_state, End)]
  | MuG (tv, _, _) when is_visited tv ->
      (* a backward epsilon link is found as a result of unfolding (see
         next). *)
      Either.Second [tv]
  | MuG (tv, _, g_type) ->
      (* visited a recursion variable for the first time. unfold it. *)
      transitions ~visited:(tv :: visited) projected_role g_type
  | TVarG (tv, _, _) when is_visited tv -> Either.First [(end_state, End)]
  | TVarG (tv, _, self) ->
      transitions ~visited:(tv :: visited) projected_role (Lazy.force self)
  | CallG (_, _, _, _) -> (* TODO *) assert false
