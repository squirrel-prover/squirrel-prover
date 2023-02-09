module L = Location
module SE = SystemExpr

type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
(** Type of a crypto assumption space (e.g. plaintext, ciphertext, key). *)
type c_ty = {
  cty_space : lsymb;
  cty_ty    : Theory.p_ty;
}

type c_tys = c_ty list

(*------------------------------------------------------------------*)
type macro_decl = {
  name      : lsymb;
  args      : Theory.bnds;
  out_ty    : Theory.p_ty option;
  init_body : Theory.term;
}

(*------------------------------------------------------------------*)
type abstract_decl = {
  name      : lsymb;
  symb_type : Symbols.symb_type;
  ty_args   : lsymb list;          (** type variables *)
  abs_tys   : Theory.p_ty;
}

(*------------------------------------------------------------------*)
type name_decl = {
  n_name : lsymb ;
  n_ty   : Theory.p_ty list;
}

(*------------------------------------------------------------------*)
type action_decl = {
  a_name : lsymb ;
  a_arity : int;
}

(*------------------------------------------------------------------*)
type bty_decl = {
  bty_name  : lsymb ;
  bty_infos : lsymb list ;
}

(*------------------------------------------------------------------*)
type system_decl = {
  sname    : Theory.lsymb option;
  sprojs   : lsymb list option;
  sprocess : Process.process;
}

let pp_system_decl fmt sys =
  let name = match sys.sname with
    | Some s -> L.unloc s
    | None -> "default" in
  Fmt.pf fmt "@[<hov 2>system %s =@ %a@]"
    name
    Process.pp_process sys.sprocess

(*------------------------------------------------------------------*)
type global_rule =
  | Rename  of Theory.global_formula
  | PRF     of Theory.bnds * Theory.term
  | PRFt    of Theory.bnds * Theory.term (* gPRF, with time *)
  | CCA     of Theory.bnds * Theory.term
  | Rewrite of TacticsArgs.rw_arg list

type system_modifier = { 
  from_sys : SE.Parse.t;
  modifier : global_rule;
  name     : Theory.lsymb
}
            

(*------------------------------------------------------------------*)
type operator_decl = { 
  op_name      : Theory.lsymb;
  op_symb_type : Symbols.symb_type;
  op_tyargs    : lsymb list;
  op_args      : Theory.ext_bnds;
  op_tyout     : Theory.p_ty option;
  op_body      : Theory.term;
}

(*------------------------------------------------------------------*)
type proc_decl = {
  id    : lsymb;
  projs : lsymb list option;
  args  : Theory.bnds;
  proc  : Process.process;
}

(*------------------------------------------------------------------*)
type orcl_tag_info = Theory.term

(*------------------------------------------------------------------*)
type declaration_i =
  | Decl_channel of lsymb
  | Decl_process of proc_decl
  | Decl_axiom   of Goal.Parsed.t
  | Decl_system  of system_decl
  | Decl_system_modifier  of system_modifier

  | Decl_dh of Symbols.dh_hyp list * lsymb *
               (lsymb * Symbols.symb_type) * 
               (lsymb * Symbols.symb_type) option * c_tys

  | Decl_hash of lsymb * orcl_tag_info option * c_tys

  | Decl_aenc of lsymb * lsymb * lsymb * c_tys

  | Decl_senc             of lsymb * lsymb * c_tys
  | Decl_senc_w_join_hash of lsymb * lsymb * lsymb

  | Decl_sign of lsymb * lsymb * lsymb * orcl_tag_info option * c_tys

  | Decl_action   of action_decl

  | Decl_name     of lsymb * Theory.p_ty option * Theory.p_ty
  | Decl_state    of macro_decl
  | Decl_operator of operator_decl
  | Decl_abstract of abstract_decl
  | Decl_bty      of bty_decl

type declaration = declaration_i Location.located

type declarations = declaration list
