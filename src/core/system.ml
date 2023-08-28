type t = Symbols.system 

(*------------------------------------------------------------------*)
let of_lsymb table s = Symbols.System.of_lsymb s table

(*------------------------------------------------------------------*)
type error =
  | Shape_error
  | Invalid_projection

let pp_error fmt = function
  | Shape_error ->
    Format.fprintf fmt "cannot register a shape twice with distinct indices"
  | Invalid_projection ->
    Format.fprintf fmt "invalid projection"

exception Error of error

let error e = raise (Error e)

(*------------------------------------------------------------------*)

module Msh = Map.Make (Action.Shape)

(** For each system we store the list of projections (which defines
    the system's arity) and a map from action shapes to action descriptions,
    which also contain action symbols. *)
type data = {
  projections : Term.proj list;
  actions     : Action.descr Msh.t
}

type Symbols.data += System_data of data

let declare_empty table system_name projections =
  assert (List.length (List.sort_uniq Stdlib.compare projections) =
          List.length projections);
  let def = () in
  let data = System_data {projections;actions=Msh.empty} in
  Symbols.System.declare_exact table system_name ~data def

let get_data table (s_symb : Symbols.system) =
  match Symbols.System.get_data s_symb table with
    | System_data data -> data
    | _ -> assert false

let projections table s = (get_data table s).projections

let valid_projection table s proj = List.mem proj (projections table s)

let descrs table s = Msh.map Action.refresh_descr (get_data table s).actions

let symbs table s = Msh.map (fun d -> d.Action.name) (get_data table s).actions

let compatible table s1 s2 =
  Msh.equal (=) (symbs table s1) (symbs table s2) &&
  let d1 = descrs table s1 in
  let d2 = descrs table s2 in
  Msh.for_all
    (fun shape d1 ->
       let d2 = Msh.find shape d2 in
       let d2 =
         let subst =
           List.map2
             (fun i j -> Term.ESubst (Term.mk_var i, Term.mk_var j))
             d2.Action.indices d1.Action.indices
         in
         Action.subst_descr subst d2
       in
       Action.strongly_compatible_descr d1 d2)
    d1

let pp_system table fmt s =
  let {actions} = get_data table s in
  let descrs = Msh.bindings actions in
  Format.fprintf fmt
    "System %a registered with actions %a.@."
    Symbols.pp s
    (Utils.pp_list (fun fmt (_,d) -> Symbols.pp fmt d.Action.name)) descrs

let pp_systems fmt table =
  Symbols.System.iter (fun sys _ _ -> pp_system table fmt sys) table

(*------------------------------------------------------------------*)
let add_action table system descr =
  (* Sanity check *)
  assert (Action.check_descr descr);

  let shape = Action.get_shape_v descr.action in
  let { actions } as data = get_data table system in
  assert (not (Msh.mem shape actions));
  let actions = Msh.add shape descr actions in
  let data = System_data { data with actions } in
  Symbols.System.redefine table system ~data ()

(*------------------------------------------------------------------*)
let descr_of_shape table system shape =
  let {actions} = get_data table system in
  let descr = Msh.find shape actions in
  assert (Action.check_descr descr);

  Action.refresh_descr descr

(** [find_shape table shape] returns [Some (name,indices)] if some
    action with name [n] and indices [i] and shape [shape] is registered
    in [table]. Return [None] if no such action exists. *)
let find_shape table shape =
  let exception Found of Symbols.action * Vars.var list in
  try
    Symbols.System.iter (fun _system () data ->
      let descrs = match data with
        | System_data {actions} -> actions
        | _ -> assert false
      in
      match Msh.find_opt shape descrs with
        | Some descr -> raise (Found (descr.name,descr.indices))
        | None -> ()
    ) table;
    None
  with Found (x,y) -> Some (x,y)

(*------------------------------------------------------------------*)
let register_action table system_symb (descr : Action.descr) =
  let Action.{ action; name = symb; indices } = descr in
  let shape = Action.get_shape_v action in
  match find_shape table shape with

  | None ->
    let table = Action.define_symbol table symb indices (Action.to_action action) in
    let table = add_action table system_symb descr in
    table, symb, descr

  | Some (_symb2, is) when List.length indices <> List.length is ->
    error Shape_error

  | Some (symb2, is) ->
    assert (Action.check_descr descr);

    let subst_action =
      List.map2 (fun i i' -> Term.ESubst (Term.mk_var i,Term.mk_var i'))
        indices is
    in
    let descr = Action.subst_descr subst_action descr in

    (* substitute the action symbol *)
    let s =
      [Term.ESubst (Term.mk_action symb (Term.mk_vars is),
                    Term.mk_action symb2 (Term.mk_vars is))] in
    let descr = Action.subst_descr s descr in    

    let descr = { descr with name = symb2 } in
    let table = add_action table system_symb descr in

    table, symb2, descr
  
(*------------------------------------------------------------------*)
(** Single systems *)

module Single = struct

  type t = {
    system     : Symbols.system ;
    projection : Term.proj
  }

  let make table system projection =
    if valid_projection table system projection then
      {system;projection}
    else
      error Invalid_projection

  let pp fmt {system;projection} =
    if Term.proj_to_string projection = "ε" then
      (* Convention typically used for single system. *)
      Format.fprintf fmt "%a" Symbols.pp system
    else
      Format.fprintf fmt "%a/%a"
        Symbols.pp system
        Term.pp_proj projection

  let descr_of_shape table {system;projection} shape =
    let multi_descr = descr_of_shape table system shape in
    let descr = Action.project_descr projection multi_descr in
    assert (Action.check_descr descr);
    descr
end
