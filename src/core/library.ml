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

  let leq_p = ([],"<=")
  let fs_leq = Symbols.Operator.of_s_path leq_p
  let mk_leq table x y = mk_fun table leq_p [x;y]
end

(*------------------------------------------------------------------*)
module Set = struct

  let check_load table =
    if not (Symbols.Import.mem_sp ([], "Set") table) then
      Tactics.hard_failure (Failure "theory Set is not loaded")
        
  let get_fsymb table s =
    check_load table;
    get_fsymb ([],s)

  let fs_mem table = get_fsymb table "mem"
  let fs_add table = get_fsymb table "add"
  let const_emptyset table = get_fsymb table "empty_set"
end  

(*------------------------------------------------------------------*)
module Int = struct
  (* namespace path *)
  let int_p = ["Int"]
 
  let check_load table =
    if not (Symbols.Import.mem_sp ([],"Int") table) then
      Tactics.hard_failure (Failure "theory Int is not loaded")

  let get_fsymb table s =
    check_load table;
    get_fsymb (int_p,s)

  let get_btype table s =
    check_load table;
    get_btype  (int_p,s)

  (*------------------------------------------------------------------*)
  let tint table = Type.base [] (Symbols.to_string (get_btype table "int").s)

  (*------------------------------------------------------------------*)
  let add   table = get_fsymb table "+"
  let minus table = get_fsymb table "-"
  let opp   table = get_fsymb table "opp"

  let mul   table = get_fsymb table "*"

  (*------------------------------------------------------------------*)
  let mk_add   table x y = Term.mk_fun table (add table)   [x;y]
  let mk_minus table x y = Term.mk_fun table (minus table) [x;y]
  let mk_opp   table x   = Term.mk_fun table (opp table)   [x]

  let mk_mul   table x y = Term.mk_fun table (mul table)   [x;y]
end

(*------------------------------------------------------------------*)
module[@warning "-32"] Real = struct

  (* namespace path *)
  let real_p = ["Real"]
 
  let check_load table =
    if not (Symbols.Import.mem_sp ([],"Real") table) then
      Tactics.hard_failure (Failure "theory Real is not loaded")

  let get_fsymb table s =
    check_load table;
    get_fsymb (real_p,s)

  let get_btype table s =
    check_load table;
    get_btype  (real_p,s)

  (*------------------------------------------------------------------*)
  let treal table = Type.base real_p (Symbols.to_string (get_btype table "real").s)

  (*------------------------------------------------------------------*)
  let fs_add   table = get_fsymb table "+"
  let fs_minus table = get_fsymb table "-"
  let fs_opp   table = get_fsymb table "opp"

  let fs_mul   table = get_fsymb table "*"
  let fs_div   table = get_fsymb table "div"
  let fs_inv   table = get_fsymb table "inv"

  let fs_zero  table = get_fsymb table "z_r"
  let fs_one   table = get_fsymb table "o_r"
  let fs_two   table = get_fsymb table "t_r"

  (*------------------------------------------------------------------*)
  let mk_add   table x y = Term.mk_fun table (fs_add table)   [x;y]
  let mk_minus table x y = Term.mk_fun table (fs_minus table) [x;y]
  let mk_opp   table x   = Term.mk_fun table (fs_opp table)   [x]

  let mk_mul   table x y = Term.mk_fun table (fs_mul table)   [x;y]
  let mk_div   table x y = Term.mk_fun table (fs_div table)   [x;y]
  let mk_inv   table x   = Term.mk_fun table (fs_inv table)   [x]

  let mk_zero  table     = Term.mk_fun table (fs_zero table)  []
  let mk_one   table     = Term.mk_fun table (fs_one  table)  []
  let mk_two   table     = Term.mk_fun table (fs_two  table)  []
end

(*------------------------------------------------------------------*)
module Secrecy = struct

  let is_loaded table =
    Symbols.Import.mem_sp ([], "WeakSecrecy") table
  let check_load table =
    if not (is_loaded table) then
      Tactics.hard_failure (Failure "theory WeakSecrecy is not loaded")
        
  let get_predicate table s =
    check_load table;
    Symbols.Predicate.of_s_path ([],s)
  
  let symb_deduce table = get_predicate table "|>"
  let symb_not_deduce table = get_predicate table "*>"
end

(*------------------------------------------------------------------*)
module Deduction = struct
  let name = "DeductionSyntax"

  let check_load_deduction_syntax table =
    if not (Symbols.Import.mem_sp ([], name) table) then
      Tactics.hard_failure (Failure "theory DeductionSyntax is not loaded")
        
  let get_predicate table s =
    check_load_deduction_syntax table;
    Symbols.Predicate.of_s_path ([],s)

  let uniform_deduction table = get_predicate table "|1>"
end  
