module L = Location

(*------------------------------------------------------------------*)
(** Not type safe, do not export.
    [np] is the namespace path, [s] the symbol name. *)
let get_fsymb (p : Symbols.s_path) : Symbols.fname =
  Symbols.Operator.of_s_path p 

let get_btype (s : Symbols.s_path) : Symbols.btype =
  try Symbols.BType.of_s_path s with
  | Symbols.Error _ -> assert false

(*------------------------------------------------------------------*)
module Prelude = struct
  (*------------------------------------------------------------------*)
  let mk_fun table str ?ty_args args =
    let symb = get_fsymb str in
    Term.mk_fun table symb ?ty_args args

  (*------------------------------------------------------------------*)
  let witness_p = ([],"witness")
  let fs_witness = get_fsymb witness_p
  let mk_witness table ~ty_arg = mk_fun table witness_p ~ty_args:[ty_arg] []

  let zeroes_p = ([],"zeroes")
  let fs_zeroes = Symbols.Operator.of_s_path zeroes_p
  let mk_zeroes table term = mk_fun table zeroes_p [term]
end

(*------------------------------------------------------------------*)
module Basic = struct

  let check_load table =
    if not (Symbols.Import.mem_sp ([], "Basic") table) then
      Tactics.hard_failure (Failure "theory Basic is not loaded")
        
  let get_fsymb table s =
    check_load table;
    get_fsymb ([],s)

  let fs_mem table = get_fsymb table "mem"
  let fs_add table = get_fsymb table "add"
  let const_emptyset table = get_fsymb table "empty_set"
end  

module Real = struct

  let check_load table =
    if not (Symbols.Import.mem_sp ([],"Real") table) then
      Tactics.hard_failure (Failure "theory Real is not loaded")

  let get_fsymb table s =
    check_load table;
    get_fsymb ([],s)

  let get_btype table s =
    check_load table;
    get_btype  ([],s)
  let real table = Type.TBase ([],Symbols.to_string (get_btype table "real").s)
  let leq table = get_fsymb table "leq"
  let add table = get_fsymb table "addr"
  let minus table = get_fsymb table "minus"
  let zero table = get_fsymb table "z_r"

  let mk_minus table x = Term.mk_fun table (minus table) [x]
  let mk_add table x y = Term.mk_fun table (add table) [x;y]
  let mk_leq table x y = Term.mk_fun table (leq table) [x;y]
  let mk_zero table    = Term.mk_fun table (zero table) []
end
