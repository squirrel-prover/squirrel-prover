open Utils

module SE = SystemExpr

(*------------------------------------------------------------------*)
(** operator body *)
type body = Term.term

type op_body = Single of body
  
type operator = {
  name    : string;
  ty_vars : Type.tvar list;
  args    : Vars.var list;
  out_ty  : Type.ty;
  body    : op_body;
}

type Symbols.data += Operator of operator

(*------------------------------------------------------------------*)
let pp_op_body fmt (Single body) = Fmt.pf fmt "%a" Term.pp body

let pp_operator fmt op =
  let pp_op_name fmt s =
    if Symbols.is_infix_str s then
      (Fmt.parens Fmt.string) fmt s 
    else
      Fmt.string fmt s
  in
  let pp_tyvars fmt tyvars =
    if tyvars = [] then () 
    else
      Fmt.pf fmt "[%a] " (Fmt.list Type.pp_tvar) tyvars
  in
  let pp_args fmt args =
    if args = [] then () 
    else
      Fmt.pf fmt "(%a) " Vars.pp_typed_list args
  in

  Fmt.pf fmt "@[<hov 2>@[op %a %a%a: %a @]=@ @[%a@]@]"
    pp_op_name op.name
    pp_tyvars op.ty_vars
    pp_args op.args
    Type.pp op.out_ty
    pp_op_body op.body

(*------------------------------------------------------------------*)
let mk ~name ~ty_vars ~args ~out_ty ~body = 
  { name; ty_vars; args; out_ty; body = Single body }

let ftype (op : operator) : Type.ftype = 
  Type.mk_ftype op.ty_vars (List.map Vars.ty op.args) op.out_ty

let is_operator (table : Symbols.table) (fsymb : Symbols.fname) : bool =
  match Symbols.Function.get_data fsymb table with
  | Operator _ -> true
  | _ -> false

(*------------------------------------------------------------------*)
let is_system_indep (table : Symbols.table) (fsymb : Symbols.fname) : bool =
  match Symbols.Function.get_data fsymb table with
  | Operator op ->
    (* for now, we only have system-independent operators so this check is 
       superfluous. *)
    begin
      match op.body with Single _ -> true
    end
  | _ -> true

(*------------------------------------------------------------------*)
let unfold 
    (table  : Symbols.table)
    (_se    : SE.arbitrary)
    (opsymb : Symbols.fname)
    (tyargs : Type.ty list)
    (args   : Term.term list)
  : Term.term
  =
  let op = 
    match Symbols.Function.get_data opsymb table with
    | Operator op -> op
    | _ -> assert false
  in

  (* apply type argument type variables *)
  let ts =
    List.fold_left2 Type.tsubst_add_tvar Type.tsubst_empty op.ty_vars tyargs
  in
  let op_args = List.map (Vars.tsubst ts) op.args in
  let op_body =
    match op.body with Single body -> Term.tsubst ts body
  in

  let i = min (List.length op_args) (List.length args) in

  (* take the [i] first arguments of [args] and [op_args] *)
  let args1   ,    args2 = List.takedrop i args    in
  let op_args1, op_args2 = List.takedrop i op_args in

  let subst = 
    List.map2 (fun x t -> 
        Term.ESubst (Term.mk_var x,t)
      ) op_args1 args1
  in
  Term.mk_app 
    (Term.subst subst
       (Term.mk_lambda ~simpl:false op_args2 op_body))
    args2 

