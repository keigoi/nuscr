open! Base
open Syntax
open Loc
open Err
open Symtable
open Names

let rec swap_role swap_role_f {value; loc} =
  let value =
    match value with
    | MessageTransfer {message; from_role; to_roles; ann} ->
        MessageTransfer
          { message
          ; from_role= swap_role_f from_role
          ; to_roles= List.map ~f:swap_role_f to_roles
          ; ann }
    | Recursion (rec_name, recvar, g) ->
        Recursion (rec_name, recvar, List.map ~f:(swap_role swap_role_f) g)
    | Continue (rec_name, exprs) -> Continue (rec_name, exprs)
    | Choice (role, gs) ->
        Choice
          ( swap_role_f role
          , List.map ~f:(List.map ~f:(swap_role swap_role_f)) gs )
    | Do (proto, roles, ann) -> Do (proto, List.map ~f:swap_role_f roles, ann)
    | Calls (caller, proto, roles, ann) ->
        Calls (swap_role_f caller, proto, List.map ~f:swap_role_f roles, ann)
  in
  {value; loc}

let instantiate (protocol : raw_global_protocol)
    (replacement_roles : RoleName.t list) =
  let original_roles = protocol.roles in
  let replacement_map = List.zip original_roles replacement_roles in
  let replacement_map =
    match replacement_map with
    | List.Or_unequal_lengths.Unequal_lengths ->
        violation ~here:[%here]
          "Must check arity before calling `instantiate`"
    | List.Or_unequal_lengths.Ok replacement_map -> replacement_map
  in
  let replacement_map =
    List.fold
      ~f:(fun acc (ori, rep) -> Map.add_exn acc ~key:ori ~data:rep)
      ~init:(Map.empty (module RoleName))
      replacement_map
  in
  let swap_f r = Map.find_exn replacement_map r in
  List.map ~f:(swap_role swap_f) protocol.interactions

let rec_var_of_protocol_roles (name, roles) loc =
  let names = ProtocolName.user name :: List.map ~f:RoleName.user roles in
  TypeVariableName.create
    (Printf.sprintf "__%s" (String.concat ~sep:"_" names))
    loc

let mk_protocol_map scr_module =
  let f acc {value= p; loc} =
    match Map.add acc ~key:p.name ~data:(p, loc, List.length p.roles) with
    | `Ok acc -> acc
    | `Duplicate ->
        let _, old_loc, _ = Map.find_exn acc p.name in
        uerr (RedefinedProtocol (p.name, loc, old_loc))
  in
  let protocols =
    List.fold ~f ~init:(Map.empty (module ProtocolName)) scr_module.protocols
  in
  protocols

module ProtocolCall = struct
  module T = struct
    type t = ProtocolName.t * RoleName.t list [@@deriving ord, sexp_of]
  end

  include T
  include Comparator.Make (T)
end

(** Unroll `do` in protocol *)
let expand_global_protocol (scr_module : scr_module)
    (protocol : global_protocol) =
  let protocols = mk_protocol_map scr_module in
  let known_roles = protocol.value.roles in
  let check_role r =
    if List.mem known_roles ~equal:RoleName.equal r then ()
    else uerr (UnboundRole r)
  in
  let maybe_add_recursion ~loc ~known (name, roles) interactions =
    let has_recursion = Map.find_exn known (name, roles) in
    let interactions =
      if has_recursion then
        [ { loc
          ; value=
              Recursion
                ( rec_var_of_protocol_roles (name, roles) loc
                , []
                , interactions ) } ]
      else interactions
    in
    interactions
  in
  let rec expand_aux known interactions =
    let expand_single known ({value; loc} as i) =
      (* known is a map to (protocol, name) -> bool
       * true indicates that the protocol has been called, meaning it is recursive;
       * false otherwise *)
      match value with
      | Do (name, roles, _annot) when Map.mem known (name, roles) ->
          let known = Map.update known (name, roles) ~f:(fun _ -> true) in
          ( known
          , [ { value=
                  Continue (rec_var_of_protocol_roles (name, roles) loc, [])
              ; loc } ] )
      | Do (name, roles, _annot) ->
          let protocol_to_expand = Map.find protocols name in
          let protocol_to_expand, _, arity =
            match protocol_to_expand with
            | Some p -> p
            | None -> uerr (UnboundProtocol name)
          in
          if List.length roles <> arity then
            uerr (ArityMismatch (name, arity, List.length roles)) ;
          List.iter ~f:check_role roles ;
          let known = Map.add_exn known ~key:(name, roles) ~data:false in
          let known, interactions =
            expand_aux known (instantiate protocol_to_expand roles)
          in
          let interactions =
            maybe_add_recursion ~loc ~known (name, roles) interactions
          in
          let known = Map.remove known (name, roles) in
          (known, interactions)
      | Recursion (r, recvars, is) ->
          let known, is = expand_aux known is in
          (known, [{i with value= Recursion (r, recvars, is)}])
      | Choice (r, iss) ->
          let known, iss = List.fold_map ~f:expand_aux ~init:known iss in
          (known, [{i with value= Choice (r, iss)}])
      | _ -> (known, [i])
    in
    let known, interactions =
      List.fold_map ~f:expand_single ~init:known interactions
    in
    (known, List.concat interactions)
  in
  let top_level = (protocol.value.name, protocol.value.roles) in
  let known, interactions =
    expand_aux
      (Map.singleton (module ProtocolCall) top_level false)
      protocol.value.interactions
  in
  let interactions =
    maybe_add_recursion ~loc:protocol.loc ~known top_level interactions
  in
  {protocol with value= {protocol.value with interactions}}

let ensure_no_nested_protocols (ast : scr_module) =
  let pragma_err =
    PragmaNotSet
      ( Pragma.show Pragma.NestedProtocols
      , "Nested protocols cannot be used without setting this pragma" )
  in
  let rec no_nested_protocols {loc= _; value= protocol} =
    let rec match_nested {loc= _; value= interaction} =
      match interaction with
      | Calls _ -> uerr pragma_err
      | Choice (_, branches) ->
          List.iter
            ~f:(fun interactions -> List.iter interactions ~f:match_nested)
            branches
      | Recursion (_, _, interactions) ->
          List.iter interactions ~f:match_nested
      | _ -> ()
    in
    let {nested_protocols; interactions; _} = protocol in
    if not (List.is_empty nested_protocols) then uerr pragma_err ;
    List.iter ~f:match_nested interactions
  in
  if not (List.is_empty ast.nested_protocols) then uerr pragma_err ;
  List.iter ast.protocols ~f:no_nested_protocols

(* Ensure all calls to global/nested protocols are valid *)
let validate_calls_in_protocols (scr_module : scr_module) =
  let rec validate_protocol_calls prefix global_table nested_table protocol =
    let rec validate_interaction protocol_roles global_table nested_table i =
      let check_role r =
        if List.mem protocol_roles ~equal:RoleName.equal r then ()
        else uerr (UnboundRole r)
      in
      let validate_call caller proto roles symbol_table =
        check_role caller ;
        List.iter ~f:check_role roles ;
        let decl = lookup_protocol symbol_table proto in
        (* Ignore dynamic roles when validating protocols, they are not
           included in the Scribble protocol*)
        let proto_roles, _ = decl.split_decl in
        let arity = List.length proto_roles in
        if arity <> List.length roles then
          uerr (ArityMismatch (proto, arity, List.length roles)) ;
        if arity <> Set.length (Set.of_list (module RoleName) roles) then
          uerr (DuplicateRoleArgs proto)
      in
      let interaction = i.value in
      match interaction with
      | Do (proto, roles, _) ->
          let fst =
            match roles with
            | hd :: _ -> hd
            | _ ->
                Err.violation ~here:[%here] "Role list should never be empty"
          in
          (*Treat Do statements as nested protocol calls with no dynamic
            participants. Let the first role be the 'caller'*)
          validate_call fst proto roles global_table
      | Calls (caller, proto, roles, _) ->
          validate_call caller proto roles nested_table
      | Recursion (_, _, is) ->
          List.iter
            ~f:
              (validate_interaction protocol_roles global_table nested_table)
            is
      | Choice (_, iss) ->
          List.iter
            ~f:(fun is ->
              List.iter
                ~f:
                  (validate_interaction protocol_roles global_table
                     nested_table )
                is )
            iss
      | _ -> ()
    in
    let new_prefix = name_with_prefix prefix protocol.value.name in
    let nested_protocols = protocol.value.nested_protocols in
    let new_nested_st =
      build_symbol_table new_prefix nested_protocols (Some nested_table)
    in
    let interactions = protocol.value.interactions in
    let roles = protocol.value.roles in
    List.iter
      ~f:(validate_interaction roles global_table new_nested_st)
      interactions ;
    List.iter
      ~f:(validate_protocol_calls new_prefix global_table new_nested_st)
      nested_protocols
  in
  let prefix = ProtocolName.of_string "" in
  let nested_symbol_table =
    build_symbol_table prefix scr_module.nested_protocols None
  in
  let global_symbol_table =
    build_symbol_table prefix scr_module.protocols None
  in
  List.iter
    ~f:
      (validate_protocol_calls prefix global_symbol_table nested_symbol_table)
    scr_module.protocols ;
  List.iter
    ~f:
      (validate_protocol_calls prefix global_symbol_table nested_symbol_table)
    scr_module.nested_protocols

(* Rename only nested protocols so they have unique ids. Global protocols and
   calls to global protocols (do <proto>(...);) remain the same *)
let rename_nested_protocols (scr_module : scr_module) =
  let module Namegen = Namegen.Make (ProtocolName) in
  let rename known name =
    ProtocolName.rename name (ProtocolName.user (Map.find_exn known name))
  in
  let update_known_protocols prefix uids known protocols =
    let update_protocol_info (uids, known) (global_protocol : global_protocol)
        =
      let proto = global_protocol.value in
      let {name; _} = proto in
      let protocol_name = name_with_prefix prefix name in
      let new_uids, protocol_name = Namegen.unique_name uids protocol_name in
      let new_known = Map.update known name ~f:(fun _ -> protocol_name) in
      let new_name =
        ProtocolName.rename name (ProtocolName.user protocol_name)
      in
      ( (new_uids, new_known)
      , {global_protocol with value= {proto with name= new_name}} )
    in
    let (new_uids, new_known), new_protocols =
      List.fold_map ~init:(uids, known) ~f:update_protocol_info protocols
    in
    ((new_uids, new_known), new_protocols)
  in
  let rec update_protocol_interactions (uids, known)
      (protocol : global_protocol) =
    let rec update_interaction known i =
      let {Loc.value= i_; _} = i in
      match i_ with
      | Calls (caller, proto, roles, ann) ->
          {i with Loc.value= Calls (caller, rename known proto, roles, ann)}
      | Recursion (name, recvars, interactions) ->
          { i with
            Loc.value=
              Recursion
                ( name
                , recvars
                , List.map ~f:(update_interaction known) interactions ) }
      | Choice (role, interactions_list) ->
          { i with
            Loc.value=
              Choice
                ( role
                , List.map
                    ~f:(List.map ~f:(update_interaction known))
                    interactions_list ) }
      | Do _ | MessageTransfer _ | Continue _ -> i
    in
    let proto = protocol.value in
    let prefix = proto.name in
    let nested_protocols = proto.nested_protocols in
    (* Update known and uids with nested protocols declarations *)
    let (new_uids, new_known), new_nested_protocols =
      update_known_protocols prefix uids known nested_protocols
    in
    (* Update references to other protocols in the protocol's interactions *)
    let new_interactions =
      List.map ~f:(update_interaction new_known) proto.interactions
    in
    (* Recursively rename nested protocols *)
    let (new_uids, _), renamed_nested_protocols =
      List.fold_map ~init:(new_uids, new_known)
        ~f:update_protocol_interactions new_nested_protocols
    in
    (* Return updated uids, original value of known (any protocols added in
       this call will be out of scope) and the updated protocol record *)
    ( (new_uids, known)
    , { protocol with
        value=
          { proto with
            nested_protocols= renamed_nested_protocols
          ; interactions= new_interactions } } )
  in
  let (uids, known), global_protocols =
    update_known_protocols
      (ProtocolName.of_string "")
      (Namegen.create ())
      (Map.empty (module ProtocolName))
      scr_module.protocols
  in
  let (uids, known), nested_protocols =
    update_known_protocols
      (ProtocolName.of_string "")
      uids known scr_module.nested_protocols
  in
  let (uids, _), renamed_global_protocols =
    List.fold_map ~init:(uids, known) ~f:update_protocol_interactions
      global_protocols
  in
  let _, renamed_nested_protocols =
    List.fold_map ~init:(uids, known) ~f:update_protocol_interactions
      nested_protocols
  in
  { scr_module with
    protocols= renamed_global_protocols
  ; nested_protocols= renamed_nested_protocols }
