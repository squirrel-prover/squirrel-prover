open Utils

module L = Location
type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
(** Type of a crypto assumption space (e.g. plaintext, ciphertext, key). *)
type c_ty = { cty_space : lsymb;
              cty_ty    : Theory.p_ty; }

type c_tys = c_ty list

(*------------------------------------------------------------------*)
type macro_decl = lsymb * Theory.bnds * Theory.p_ty * Theory.term

(*------------------------------------------------------------------*)
type abstract_decl = { name    : lsymb;
                       symb_type : Symbols.symb_type;
                       ty_args : lsymb list; (* type variables *)
                       abs_tys : Theory.p_ty list; }

(*------------------------------------------------------------------*)
type name_decl = { n_name : lsymb ;
                   n_type : Theory.p_ty list; }

(*------------------------------------------------------------------*)
type bty_decl = { bty_name  : lsymb ;
                  bty_infos : Symbols.bty_info list ; }

(*------------------------------------------------------------------*)
type system_decl = { sname    : Theory.lsymb option;
                     sprocess : Process.process; }

let pp_system_decl fmt sys =
  let name = match sys.sname with
    | Some s -> L.unloc s
    | None -> "default" in
  Fmt.pf fmt "@[<hov 2>system %s =@ %a@]"
    name
    Process.pp_process sys.sprocess

(*------------------------------------------------------------------*)
type orcl_tag_info = Theory.formula

let pp_orcl_tag_info = Theory.pp

(*------------------------------------------------------------------*)
type declaration_i =
  | Decl_channel of lsymb
  | Decl_process of lsymb * Theory.bnds * Process.process
  | Decl_axiom   of Goal.Parsed.t
  | Decl_system  of system_decl

  | Decl_ddh of lsymb * (lsymb * Symbols.symb_type) * c_tys 

  | Decl_hash of int option * lsymb * orcl_tag_info option * c_tys 

  | Decl_aenc of lsymb * lsymb * lsymb * c_tys 

  | Decl_senc             of lsymb * lsymb * c_tys 
  | Decl_senc_w_join_hash of lsymb * lsymb * lsymb

  | Decl_sign of lsymb * lsymb * lsymb * orcl_tag_info option * c_tys 

  | Decl_name     of lsymb * int * Theory.p_ty
  | Decl_state    of macro_decl
  | Decl_abstract of abstract_decl
  | Decl_bty      of bty_decl

type declaration = declaration_i Location.located

type declarations = declaration list
