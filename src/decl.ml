
type macro_decl = string * (string * Sorts.esort) list * Sorts.esort * Theory.term 

type abstract_decl = { name          : string;
                       index_arity   : int;
                       message_arity : int; }

type goal_decl = { gname   : string option;
                   gsystem : Action.system;
                   gform   : Theory.formula; }

type system_decl = { sname    : Action.system_name option;
                     sprocess : Process.process; }

type declaration =
  | Decl_channel of string
  | Decl_process of Process.id * Process.pkind * Process.process
  | Decl_axiom   of goal_decl
  | Decl_system  of system_decl

  | Decl_hash             of int option * string * orcl_tag_info option
  | Decl_aenc             of string * string * string
  | Decl_senc             of string * string                 
  | Decl_senc_w_join_hash of string * string * string
  | Decl_sign             of string * string * string * orcl_tag_info option
  | Decl_name             of string * int 
  | Decl_state            of string * int * Sorts.esort
  | Decl_abstract         of abstract_decl
  | Decl_macro            of macro_decl

type declarations = declaration list

let declare_list decls = List.fold_left (fun () d -> declare d) () decls
