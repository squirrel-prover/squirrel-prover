module L = Location
type lsymb = Symbols.lsymb

(*------------------------------------------------------------------*)
include Symbols.System

type system_name = Symbols.system Symbols.t

(*------------------------------------------------------------------*)
type system_error = 
  | SE_ShapeError

let pp_system_error fmt = function
  | SE_ShapeError -> 
    Fmt.pf fmt "cannot register a shape twice with distinct indices" 

exception SystemError of system_error

let system_err e = raise (SystemError e)
(*------------------------------------------------------------------*)
module ShapeCmp = struct
  type t = Action.shape
  let rec compare (u : t) (v : t) = Stdlib.compare u v
end

module Msh = Map.Make (ShapeCmp)

(** For each system we maintain two tables:
  * the first one associates to each valid shape the corresponding
  * action description;
  * the second one maps each shapes of valid or dummy actions to
  * their corresponding symbols.
  * There is some redundancy: the symbol of a dummy action can also
  * be obtained through the first map, but this avoids a double lookup. *)
type Symbols.data += System_data of Action.descr Msh.t * Symbols.action Symbols.t Msh.t

let of_string (name : lsymb) (table : Symbols.table) =
  Symbols.System.of_lsymb name table 

let declare_empty table system_name =
  let def = () in
  let data = System_data (Msh.empty,Msh.empty) in
  Symbols.System.declare_exact table system_name ~data def 

(*------------------------------------------------------------------*)
let get_data table s_symb =
  match Symbols.System.get_data s_symb table with
    | System_data (m,d) -> m,d
    | _ -> assert false

let descrs table s = fst (get_data table s)
let symbs table s = snd (get_data table s)

let pp_system table fmt s =
  let descrs,symbs = get_data table s in
  let descrs = Msh.bindings descrs in
    Format.printf "System %a registered with actions %a.@."
      Symbols.pp s
      (Utils.pp_list (fun fmt (_,d) -> Symbols.pp fmt d.Action.name)) descrs

let pp_systems fmt table =
  Symbols.System.iter (fun sys _ _ -> pp_system table fmt sys) table

(*------------------------------------------------------------------*)
let add_action
    (table : Symbols.table) (s_symb : Symbols.system Symbols.t)
    (shape : Action.shape)  (action : Symbols.action Symbols.t)
    (descr : Action.descr) =
  (* Sanity checks *)
  assert (shape = Action.get_shape descr.action);
  assert (Action.get_indices descr.action = descr.indices);
  assert (action = descr.name);
  let descrs,symbs = get_data table s_symb in
  assert (not (Msh.mem shape descrs || Msh.mem shape symbs));
  let descrs = Msh.add shape descr descrs in
  let symbs = Msh.add shape descr.name symbs in
  let data = System_data (descrs,symbs) in
  Symbols.System.redefine table s_symb ~data ()

(*------------------------------------------------------------------*)
let descr_of_shape table (system : Symbols.system Symbols.t) shape =
  let descrs,_ = get_data table system in
  Msh.find shape descrs

(** We look whether the shape already has a name in another system,
    with the same number of indices.
    If that is the case, use the same symbol. *)
let find_shape table shape =
  let exception Found of Symbols.action Symbols.t * Vars.index list in
  try Symbols.System.iter (fun system () data ->
      let descrs = match data with
        | System_data (descrs,_) -> descrs
        | _ -> assert false in
      if Msh.mem shape descrs then 
        let descr = Msh.find shape descrs in
        raise (Found (descr.name, descr.indices))
      else ()
    ) table; 
    None
  with Found (x,y) -> Some (x,y)

(*------------------------------------------------------------------*)

(** Define dummy action symbols in table and register them
  * in the map symbs from shapes to symbols. *)
let rec define_dummies table symbs len =
  let table,symbs =
    if len>0 then define_dummies table symbs (len-1) else table,symbs
  in
  let dummy = Action.dummy len in
  let dum_shape = Action.get_shape dummy in
  if Msh.mem dum_shape symbs then table,symbs else
  let table,dum_symb = 
    Action.fresh_symbol ~exact:false table (L.mk_loc Location._dummy "_Dummy") 
  in
  let table = Action.define_symbol table dum_symb [] dummy in
  let symbs = Msh.add dum_shape dum_symb symbs in
  table,symbs

let register_action table system_symb symb indices action descr =
  let shape = Action.get_shape action in
  match find_shape table shape with
  | Some (symb2, is) when List.length indices <> List.length is ->
      system_err SE_ShapeError

  | Some (symb2, is) ->
    let subst_action =
      [Term.ESubst (Term.Action (symb,indices), Term.Action (symb2,is))]
    in
    (* Careful, the substitution does not substitute the action symbol
       [symb] by [symb2], nor the indices. We must do it manually. *)
    let descr = Action.subst_descr subst_action descr in 

    let subst_is =
      List.map2 (fun i i' -> Term.ESubst (Term.Var i,Term.Var i'))
        indices is
    in
    let descr = Action.subst_descr subst_is descr in
    let descr = { descr with name = symb2 } in
    let table = add_action table system_symb shape symb2 descr in
    table, symb2, descr

  | None ->
    (* Define the already existing symbol. *)
    let table = Action.define_symbol table symb indices action in
    (* Add action description to system. *)
    let table = add_action table system_symb shape symb descr in
    (* Define dummy action symbol if needed. *)
    let descrs,symbs = get_data table system_symb in
    let table,symbs = define_dummies table symbs (List.length action) in
    let data = System_data (descrs,symbs) in
    let table = Symbols.System.redefine table system_symb ~data () in
    table, symb, descr
