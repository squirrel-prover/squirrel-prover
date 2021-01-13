include Symbols.System

type system_name = Symbols.system Symbols.t

(*------------------------------------------------------------------*)
type system_error = 
  | SE_ShapeError
  | SE_UnknownSystem of string
  | SE_SystemAlreadyDefined of string

let pp_system_error fmt = function
  | SE_ShapeError -> 
    Fmt.pf fmt "cannot register a shape twice with distinct indices." 
  | SE_UnknownSystem s -> 
    Fmt.pf fmt "system [%s] unknown" s
  | SE_SystemAlreadyDefined s -> 
    Fmt.pf fmt "system [%s] already defined" s

exception SystemError of system_error

let system_err e = raise (SystemError e)
(*------------------------------------------------------------------*)
module ShapeCmp = struct
  type t = Action.shape
  (* The minus allows to iter over the shapes in the same order that we 
     used to. *)
  let rec compare (u : t) (v : t) = - (Stdlib.compare u v)
end

module Msh = Map.Make (ShapeCmp)

type Symbols.data += System_data of Action.descr Msh.t

let of_string system_name (table : Symbols.table) =
  try Symbols.System.of_string system_name table with
  | Symbols.Unbound_identifier _ -> 
    system_err (SE_UnknownSystem system_name)

let declare_empty table system_name =
    let def = () in
    let data = System_data Msh.empty in
    try Symbols.System.declare_exact table system_name ~data def with
    | Symbols.Multiple_declarations _ ->
      system_err (SE_SystemAlreadyDefined system_name)

(*------------------------------------------------------------------*)
let is_fresh s_str table =
  try ignore (Symbols.System.of_string s_str table); false
  with Symbols.Unbound_identifier _ -> true

let descrs table s_symb = 
  match Symbols.System.get_all s_symb table with
    | (), System_data m -> m
    | _ -> assert false

let add_action 
    (table : Symbols.table) (s_symb : Symbols.system Symbols.t) 
    (shape : Action.shape)  (action : Symbols.action Symbols.t) 
    (descr : Action.descr) =
  let descrs = descrs table s_symb in
  if Msh.mem shape descrs 
  then assert false             (* should be impossible *)
  else 
    let descrs = Msh.add shape descr descrs in
    let data = System_data descrs in
    Symbols.System.redefine table s_symb ~data ()

(*------------------------------------------------------------------*)
let descr_of_shape table (system : Symbols.system Symbols.t) shape = 
  let descrs = descrs table system in
  Msh.find shape descrs 

let shape_bound table (system : Symbols.system Symbols.t) shape =
  let descrs = descrs table system in
  Msh.mem shape descrs 

(*------------------------------------------------------------------*)
let shape_to_symb table system_symb shape = 
  let descr = descr_of_shape table system_symb shape in
  descr.Action.name

let action_to_term table system_symb (a : Action.action) =
  let descr = descr_of_shape table system_symb (Action.get_shape a) in
  let indices = descr.Action.indices in
  Term.Action (descr.name, indices)

let rec dummy_action (* system table *) k = assert false (* TODO *)
  (* let open Action in
   * let a =
   *   if k = 0 then [] else
   *     { par_choice = 0,[] ; sum_choice = 0,[] } :: dummy_action (k-1)
   * in
   * let s = Action.get_shape a in
   * let data = Data ([],a) in
   * if not (Hashtbl.mem shape_to_symb s) then
   *   Hashtbl.add shape_to_symb s
   *     (snd
   *        (Symbols.Action.declare 
   *           (assert false) (* TODO: used to be Symbols.dummy_table *)
   *           "_Dummy" ~data 0)) ;
   * a *)

(*------------------------------------------------------------------*)

let register_action table system_symb symb indices action descr =
  let shape = Action.get_shape action in

  match action_to_term table system_symb action with
  | Term.Action (symb2, is) when indices <> is ->
      system_err SE_ShapeError

  | Term.Action (symb2, is) ->
      let subst =
        Term.ESubst (Term.Action (symb,is), Term.Action (symb2,is)) in
      let descr = Action.subst_descr [subst] descr in 
      assert (descr.action = action); 
      let table = add_action table system_symb shape symb2 descr in
      table, symb2

  | _ -> assert false

  | exception Not_found ->    
      let table = Action.define_symbol table symb indices action in
      let table = add_action table system_symb shape symb descr in
      table, symb
