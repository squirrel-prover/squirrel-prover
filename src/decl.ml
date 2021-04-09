open Utils

module L = Location
type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
let pp_type fmt (l : (Type.ety * int) list) =
  let pp_single fmt (k,i) = match i with
    | 0 -> ()
    | i ->
      assert (i > 0);
      Fmt.pf fmt "%a^%d" Type.pp_e k i
  in
  (Fmt.list ~sep:(fun fmt () -> Fmt.pf fmt " →@ ") pp_single) fmt l

let pp_args fmt (l : (string * Type.ety) list) =
  let pp_single fmt (s,k) = Fmt.pf fmt "(%s : %a)" s Type.pp_e k in
  (Fmt.list ~sep:(fun fmt () -> Fmt.pf fmt " →@ ") pp_single) fmt l

(*------------------------------------------------------------------*)
type macro_decl = lsymb * (lsymb * Type.ety) list * Type.ety * Theory.term

let pp_macro_decl fmt (s, args, k, t) =
  Fmt.pf fmt "@[<hov 2>term %s : %a → %a =@ %a@]" (L.unloc s)
    pp_args (List.map (fun (x,y) -> (L.unloc x, y)) args)
    Type.pp_e k Theory.pp t

(*------------------------------------------------------------------*)
type abstract_decl = { name    : lsymb;
                       ty_args : lsymb list; (* type variables *)
                       abs_tys : Theory.p_ty list; }

let parse_abstract_decl table decl =
    let in_tys, out_ty =
      List.takedrop (List.length decl.abs_tys - 1) decl.abs_tys
    in
    let out_ty = as_seq1 out_ty in

    let ty_args = List.map (fun l ->
        let id = Ident.create (L.unloc l) in
        Type.tvar_of_ident id
      ) decl.ty_args
    in

    let in_tys = List.map (Theory.parse_p_ty table ty_args) in_tys in

    let rec parse_in_tys p_tys : Type.message Type.ty list  =
      match p_tys with
      | [] -> []
      | (Type.ETy ty) :: in_tys -> match Type.kind ty with
        | Type.KMessage -> ty :: parse_in_tys in_tys
        | Type.KIndex -> assert false
        | Type.KTimestamp -> assert false
        | Type.KBoolean -> assert false
    in
          
    let rec parse_index_prefix iarr in_tys = match in_tys with
      | [] -> iarr, []
      | (Type.ETy ty) :: in_tys as in_tys0 ->
        match Type.kind ty with
        | Type.KIndex -> parse_index_prefix (iarr + 1) in_tys
        | _ -> iarr, parse_in_tys in_tys0
    in

    let iarr, in_tys = parse_index_prefix 0 in_tys in

    let out_ty : Type.message Type.ty =
      match Theory.parse_p_ty table ty_args out_ty with
      | Type.ETy ty -> match Type.kind ty with
        | Type.KMessage -> ty
        | _ -> assert false
    in
    
    Theory.declare_abstract
      table decl.name
      ~index_arity:iarr
      ~ty_args
      ~in_tys
      ~out_ty

(*------------------------------------------------------------------*)
type goal_decl = { gname   : lsymb option ;
                   gsystem : SystemExpr.p_system_expr ;
                   gform   : Theory.formula ; }

let pp_goal_decl fmt decl =
  let name = match decl.gname with
    | Some s -> L.unloc s
    | None -> "_?" in
  Fmt.pf fmt "@[<hov 2>axiom [%a] %s =@ %a@]"
    SystemExpr.pp_p_system decl.gsystem
    name
    Theory.pp decl.gform

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
  | Decl_process of lsymb * (lsymb * Type.ety) list * Process.process
  | Decl_axiom   of goal_decl
  | Decl_system  of system_decl

  | Decl_hash             of int option * lsymb * orcl_tag_info option
  | Decl_aenc             of lsymb * lsymb * lsymb
  | Decl_senc             of lsymb * lsymb
  | Decl_senc_w_join_hash of lsymb * lsymb * lsymb
  | Decl_sign             of lsymb * lsymb * lsymb * orcl_tag_info option
  | Decl_name             of lsymb * int
  | Decl_state            of macro_decl
  | Decl_abstract         of abstract_decl
  | Decl_macro            of macro_decl

type declaration = declaration_i Location.located

type declarations = declaration list
