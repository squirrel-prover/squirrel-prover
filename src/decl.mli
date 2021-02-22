(** Syntax of declarations parsed by the prover. The processing of the
    declarations is done later, in the Prover module. *)

type lsymb = Theory.lsymb

(** { 1 Declarations } *)

(** Information for a macro declaration *)
type macro_decl = string * (lsymb * Sorts.esort) list * Sorts.esort * Theory.term

val pp_macro_decl : Format.formatter -> macro_decl -> unit

(** Information for an abstract declaration *)
type abstract_decl = { name          : string;
                       index_arity   : int;
                       message_arity : int; }

val pp_abstract_decl : Format.formatter -> abstract_decl -> unit

(** Information for a goal or axiom declaration *)
type goal_decl = { gname   : string option;
                   gsystem : SystemExpr.p_system_expr;
                   gform   : Theory.formula; }

val pp_goal_decl : Format.formatter -> goal_decl -> unit

(** Information for a system declaration *)
type system_decl = { sname    : string option;
                     sprocess : Process.process; }

val pp_system_decl : Format.formatter -> system_decl -> unit

(** Additional oracle tagging information
    Allows to define the tag formula corresponding to some function.
    Defining a function with such a tag, is equivalent to giving to the
    attacker a backdoor, allowing to compute the ouput of the function on
    all messages that satisfy the tag. *)
type orcl_tag_info = Theory.formula

val pp_orcl_tag_info : Format.formatter -> orcl_tag_info -> unit

(** Declarations *)
type declaration_i =
  | Decl_channel of string
  | Decl_process of lsymb * (lsymb * Sorts.esort) list * Process.process
  | Decl_axiom   of goal_decl
  | Decl_system  of system_decl

  | Decl_hash             of int option * string * orcl_tag_info option
  | Decl_aenc             of string * string * string
  | Decl_senc             of string * string
  | Decl_senc_w_join_hash of string * string * lsymb
  | Decl_sign             of string * string * string * orcl_tag_info option
  | Decl_name             of string * int
  | Decl_state            of macro_decl
  | Decl_abstract         of abstract_decl
  | Decl_macro            of macro_decl

type declaration = declaration_i Location.located

type declarations = declaration list

(*------------------------------------------------------------------*)
(** {2 Debugging pretty printers}*)

(** Do not print the location information. *)
val pp_decl  : Format.formatter -> declaration  -> unit

(** Do not print the location information. *)
val pp_decls : Format.formatter -> declarations -> unit
