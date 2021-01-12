include Symbols.System

type system_name = Symbols.system Symbols.t


(*------------------------------------------------------------------*)
module ShapeCmp = struct
  type t = Action.shape
  let rec compare (u : t) (v : t) = match u,v with
    | a :: u, b :: v -> 
      let res = Stdlib.compare a b in
      if res = 0 then compare u v
      else res
    | _ :: _, [] -> -1
    | [], _ :: _ -> 1
    | [], [] -> 0
end

module Msh = Map.Make (ShapeCmp)

type Symbols.data += System_data of Action.descr Msh.t

let is_fresh s_str table =
  try ignore (Symbols.System.of_string s_str table); false
  with Symbols.Unbound_identifier _ -> true

let get_or_create_system table s_str = 
  try
    let s_symb = Symbols.System.of_string s_str table in
    table, s_symb
  with
  | Symbols.Unbound_identifier _ ->
    let def = () in
    let data = System_data Msh.empty in
    Symbols.System.declare_exact table s_str ~data def

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

let descr_of_shape table (system : Symbols.system Symbols.t) shape = 
  let descrs = descrs table system in
  Msh.find shape descrs 


(*------------------------------------------------------------------*)
let shape_to_symb table system_symb shape = 
  let descr = descr_of_shape table system_symb shape in
  descr.Action.action

let to_term (a : action)  =
  let indices = indices a in
  Term.Action (Hashtbl.find shape_to_symb (get_shape a), indices)



(*------------------------------------------------------------------*)
exception SystemError of string

let register_action table s_str symb indices action descr =
  let shape = Action.get_shape action in
  let table, system = get_or_create_system table s_str in

  match Action.to_term action with
  | Term.Action (symb2, is) when indices <> is ->
      raise @@
      SystemError "Cannot register a shape twice with distinct indices."

  | Term.Action (symb2, is) ->
      let subst =
        Term.ESubst (Term.Action (symb,is), Term.Action (symb2,is)) in
      let descr = Action.subst_descr [subst] descr in 
      assert (descr.action = action); 
      let table = add_action table system shape symb2 descr in
      table, symb2

  | _ -> assert false

  | exception Not_found ->    
      let table = Action.define_symbol table symb indices action in
      let table = add_action table system shape symb descr in
      table, symb
