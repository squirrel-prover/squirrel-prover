(** Syntax of declarations parsed by the prover. The processing of the
    declarations is done later, in the Prover module. *)

(** { 1 Declarations } *)

(** Information for a macro declaration *)
type macro_decl = string * (string * Sorts.esort) list * Sorts.esort * Theory.term 

(** Information for an abstract declaration *)
type abstract_decl = { name          : string;
                       index_arity   : int;
                       message_arity : int; }


(** Information for a goal or axiom declaration *)
type goal_decl = { gname   : string option;
                   gsystem : Action.system;
                   gform   : Theory.formula; }

(** Information for a system declaration *)
type system_decl = { sname    : Action.system_name option;
                     sprocess : Process.process; }

(** Additional oracle tagging information
    Allows to define the tag formula corresponding to some function.
    Defining a function with such a tag, is equivalent to giving to the
    attacker a backdoor, allowing to compute the ouput of the function on
    all messages that satisfy the tag. *)
type orcl_tag_info = Theory.formula
(** Declarations *)
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

(** Process a declaration. *)
val declare      : declaration  -> unit
val declare_list : declarations -> unit
