module L = Location
module SE = SystemExpr

(** Syntax of declarations parsed by the prover. The processing of the
    declarations is done later, in the Prover module. *)

type lsymb = Symbols.lsymb

(*------------------------------------------------------------------*)
(** {2 Declarations } *)

(*------------------------------------------------------------------*)
(** Type of a crypto assumption space (e.g. plaintext, ciphertext, key). *)
type c_ty = {
  cty_space : lsymb;
  cty_ty    : Typing.ty;
}

type c_tys = c_ty list

(*------------------------------------------------------------------*)
(** Information for a macro declaration *)
type state_macro_decl = {
  name      : lsymb;
  args      : Typing.bnds;
  out_ty    : Typing.ty option;
  init_body : Typing.term;
}

(*------------------------------------------------------------------*)
(** Information for a mutex declaration *)
type mutex_decl = {
  name      : lsymb;
  arity : int;
}

(*------------------------------------------------------------------*)
(** Information for a name declaration *)
type name_decl = {
  n_name : lsymb ;
  n_ty   : Typing.ty list;
}

(*------------------------------------------------------------------*)
(** Information for an action declaration *)
type action_decl = {
  a_name  : lsymb ;
  a_arity : int;
}

(*------------------------------------------------------------------*)
(** Information for a base type declaration *)
type bty_decl = {
  bty_name  : lsymb ;
  bty_infos : lsymb list ;
}

(*------------------------------------------------------------------*)
(** Information for a system declaration *)
type system_decl = {
  sname         : Symbols.lsymb option;
  system_option : Symbols.lsymb option;
  sprojs        : lsymb list option;
  sprocess      : Process.Parse.t;
}

(*------------------------------------------------------------------*)
(** Information for a system declaration using a global modifier    *)

(** Global cryptographic rules *)
type global_rule =
  | Rename  of Typing.global_formula
  | PRF     of Typing.bnds * Typing.term
  | CCA     of Typing.bnds * Typing.term
  | Rewrite of TacticsArgs.rw_arg list

(** System modifier, comprising:
    the original system, the global rule to apply, and the name of 
    the new system. *)
type system_modifier = { 
  from_sys : SE.Parse.t;
  modifier : global_rule;
  name     : Symbols.lsymb
}

type op_kind =  [`Op | `Let of [`NoRec | `Rec | `RecWithOrd of Symbols.p_path]]
  (** - [`Op] is for an abstract or concrete operator (i.e. `adv`)
      - [`Let is_rec] is for a arbitrary functions, which are:
        * [`Rec] recursive and well-founded with the ordering <
        * [`RecWithOrd sx] recursive and well-founded with the ordering [sx]
        * [`NoRec] not recursive.
  *)

type  op_in_system = [`Any | `Systems of SE.Parse.t | `Like of Symbols.p_path]
type  op_tyargs    = lsymb list

(*------------------------------------------------------------------*)
(** An operator or a let definition or declaration. *)
type fun_decl = { 
  op_name      : Symbols.lsymb;
  op_symb_type : Symbols.symb_type;
  op_args      : Typing.ext_bnds;
  op_tyout     : Typing.ty option;
  op_body      : [
    | `Concrete of Typing.term
    | `Match    of Typing.match_body
    | `Abstract
  ];
 op_terby      : Typing.term option
}

(*------------------------------------------------------------------*)
(** Information for a predicate declaration *)
type predicate_decl = { 
  pred_name       : Symbols.lsymb;
  pred_symb_type  : Symbols.symb_type;
  pred_tyargs     : lsymb list;
  pred_se_args    : SE.p_bnds;
  (** system variable, system information *)
  pred_multi_args : (lsymb * Typing.bnds) list;
  (** system variable, mutli-term variables *)
  pred_simpl_args : Typing.bnds;
  pred_body       : Typing.global_formula option;
}

(*------------------------------------------------------------------*)
(** Processus declaration *)
type proc_decl = {
  id    : lsymb;
  projs : lsymb list option;
  args  : Typing.bnds;
  proc  : Process.Parse.t;
}

(*------------------------------------------------------------------*)
(** Information for a namespace *)
type namespace_info =
  | Enter of Symbols.p_npath
  | Exit  of Symbols.p_npath
  | Open  of Symbols.p_npath
  | Close of Symbols.p_npath

(*------------------------------------------------------------------*)
(** Additional oracle tagging information
    Allows to define the tag formula corresponding to some function.
    Defining a function with such a tag, is equivalent to giving to the
    attacker a backdoor, allowing to compute the ouput of the function on
    all messages that satisfy the tag. *)
type orcl_tag_info = Typing.term

(*------------------------------------------------------------------*)
(** {2 Declarations} *)

type declaration_i =
  | Decl_channel of lsymb
  | Decl_process of proc_decl
  | Decl_axiom   of Goal.Parsed.t
  | Decl_system  of system_decl
  | Decl_system_modifier  of system_modifier

  | Decl_dh of
      Symbols.OpData.dh_hyp list * lsymb * 
      (lsymb * Symbols.symb_type) * 
      (lsymb * Symbols.symb_type) option * c_tys

  | Decl_hash of lsymb * orcl_tag_info option * c_tys

  | Decl_aenc of lsymb * lsymb * lsymb * c_tys

  | Decl_senc             of lsymb * lsymb * c_tys
  | Decl_senc_w_join_hash of lsymb * lsymb * Symbols.p_path

  | Decl_sign of lsymb * lsymb * lsymb * orcl_tag_info option * c_tys

  | Decl_action    of action_decl
  | Decl_name      of lsymb * Typing.ty
  | Decl_state     of state_macro_decl
  | Decl_mutex     of mutex_decl
  | Decl_funs      of op_kind * op_in_system * op_tyargs * fun_decl list
  | Decl_predicate of predicate_decl
  | Decl_bty       of bty_decl
  | Decl_game      of Crypto.Parse.game_decl
  | Namespace_cmd  of namespace_info
  | Tactic         of lsymb * ProverTactics.AST.t

type declaration = declaration_i L.located

type declarations = declaration list
