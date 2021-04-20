(** Syntax of declarations parsed by the prover. The processing of the
    declarations is done later, in the Prover module. *)

type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
(** {2 Declarations } *)

(** Information for a macro declaration *)
type macro_decl = lsymb * Theory.bnds * Theory.p_ty * Theory.term

(*------------------------------------------------------------------*)
(** Information for an abstract declaration *)
type abstract_decl = { name    : lsymb;
                       ty_args : lsymb list; (* type variables *)
                       abs_tys : Theory.p_ty list; }

(*------------------------------------------------------------------*)
(** Information for a name declaration *)
type name_decl = { n_name : lsymb ;
                   n_type : Theory.p_ty list; }

(*------------------------------------------------------------------*)
(** Information for a base type declaration *)
type bty_decl = { bty_name  : lsymb ;
                  bty_infos : Symbols.bty_info list ; }

(*------------------------------------------------------------------*)
(** Information for a goal or axiom declaration *)
type goal_decl = { gname   : lsymb option;
                   gsystem : SystemExpr.p_system_expr;
                   gform   : Theory.formula; }

val pp_goal_decl : Format.formatter -> goal_decl -> unit

(*------------------------------------------------------------------*)
(** Information for a system declaration *)
type system_decl = { sname    : Theory.lsymb option;
                     sprocess : Process.process; }

val pp_system_decl : Format.formatter -> system_decl -> unit

(*------------------------------------------------------------------*)
(** Additional oracle tagging information
    Allows to define the tag formula corresponding to some function.
    Defining a function with such a tag, is equivalent to giving to the
    attacker a backdoor, allowing to compute the ouput of the function on
    all messages that satisfy the tag. *)
type orcl_tag_info = Theory.formula

val pp_orcl_tag_info : Format.formatter -> orcl_tag_info -> unit

(*------------------------------------------------------------------*)
(** {2 Declarations} *)
  
type declaration_i =
  | Decl_channel of lsymb
  | Decl_process of lsymb * Theory.bnds * Process.process
  | Decl_axiom   of goal_decl
  | Decl_system  of system_decl

  | Decl_hash             of int option * lsymb * orcl_tag_info option
  | Decl_aenc             of lsymb * lsymb * lsymb
  | Decl_senc             of lsymb * lsymb
  | Decl_senc_w_join_hash of lsymb * lsymb * lsymb
  | Decl_sign             of lsymb * lsymb * lsymb * orcl_tag_info option
  | Decl_name             of lsymb * int * Theory.p_ty
  | Decl_state            of macro_decl
  | Decl_abstract         of abstract_decl
  | Decl_macro            of macro_decl
  | Decl_bty              of bty_decl

type declaration = declaration_i Location.located

type declarations = declaration list
