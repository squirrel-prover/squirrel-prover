module L = Location

(*------------------------------------------------------------------*)
(** Not type safe, do not export.
    [np] is the namespace path, [s] the symbol name. *)
let get_fsymb (p : Symbols.s_path) : Symbols.fname =
  Symbols.Operator.of_s_path p 

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
