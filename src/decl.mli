(** Syntax of declarations parsed by the prover. The processing of the
    declarations is done later, in the Prover module. *)

type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
(** {2 Declarations } *)

(*------------------------------------------------------------------*)
(** Type of a crypto assumption space (e.g. plaintext, ciphertext, key). *)
type c_ty = {
  cty_space : lsymb;
  cty_ty    : Theory.p_ty;
}

type c_tys = c_ty list

(*------------------------------------------------------------------*)
(** Information for a macro declaration *)
type macro_decl = lsymb * Theory.bnds * Theory.p_ty * Theory.term

(*------------------------------------------------------------------*)
(** Information for an abstract declaration *)
type abstract_decl = {
  name      : lsymb;
  symb_type : Symbols.symb_type;
  ty_args   : lsymb list;          (** type variables *)
  abs_tys   : Theory.p_ty list;
}

(*------------------------------------------------------------------*)
(** Information for a name declaration *)
type name_decl = {
  n_name : lsymb ;
  n_ty   : Theory.p_ty list;
}

(*------------------------------------------------------------------*)
(** Information for a base type declaration *)
type bty_decl = {
  bty_name  : lsymb ;
  bty_infos : Symbols.bty_info list ;
}

(*------------------------------------------------------------------*)
(** Information for a system declaration *)
type system_decl = {
  sname    : Theory.lsymb option;
  sprojs   : lsymb list option;
  sprocess : Process.process;
}

val pp_system_decl : Format.formatter -> system_decl -> unit

(*------------------------------------------------------------------*)
(** Information for a system declaration using a global modifier    *)

(** Global cryptographic rules *)
type global_rule =
  | Rename of Theory.global_formula
  | PRF    of Theory.bnds * Theory.term
  | PRFt   of Theory.bnds * Theory.term (* gPRF, with time *)
  | CCA    of Theory.bnds * Theory.term

(** System modifier, comprising:
    the original system, the global rule to apply, and the name of 
    the new system. *)
type system_modifier = { 
  from_sys : SystemExpr.parsed_t;
  modifier : global_rule;
  name     : Theory.lsymb
}
                          
(*------------------------------------------------------------------*)
(** Information for an operator declaration *)
type operator_decl = { 
  op_name   : Theory.lsymb;
  op_tyargs : lsymb list;
  op_args   : Theory.bnds;
  op_tyout  : Theory.p_ty option;
  op_body   : Theory.term;
}

(*------------------------------------------------------------------*)
(** Processus declaration *)
type proc_decl = {
  id    : lsymb;
  projs : lsymb list option;
  args  : Theory.bnds;
  proc  : Process.process;
}

(*------------------------------------------------------------------*)
(** Additional oracle tagging information
    Allows to define the tag formula corresponding to some function.
    Defining a function with such a tag, is equivalent to giving to the
    attacker a backdoor, allowing to compute the ouput of the function on
    all messages that satisfy the tag. *)
type orcl_tag_info = Theory.term

val pp_orcl_tag_info : Format.formatter -> orcl_tag_info -> unit

(*------------------------------------------------------------------*)
(** {2 Declarations} *)

type declaration_i =
  | Decl_channel of lsymb
  | Decl_process of proc_decl
  | Decl_axiom   of Goal.Parsed.t
  | Decl_system  of system_decl
  | Decl_system_modifier  of system_modifier

  | Decl_dh of Symbols.dh_hyp list * lsymb * (lsymb * Symbols.symb_type) * (lsymb * Symbols.symb_type) option * c_tys

  | Decl_hash of int option * lsymb * orcl_tag_info option * c_tys

  | Decl_aenc of lsymb * lsymb * lsymb * c_tys

  | Decl_senc             of lsymb * lsymb * c_tys
  | Decl_senc_w_join_hash of lsymb * lsymb * lsymb

  | Decl_sign of lsymb * lsymb * lsymb * orcl_tag_info option * c_tys

  | Decl_name     of lsymb * Theory.p_ty list
  | Decl_state    of macro_decl
  | Decl_operator of operator_decl
  | Decl_abstract of abstract_decl
  | Decl_bty      of bty_decl

type declaration = declaration_i Location.located

type declarations = declaration list
