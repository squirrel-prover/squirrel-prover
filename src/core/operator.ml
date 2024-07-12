open Utils

module SE = SystemExpr

(*------------------------------------------------------------------*)
type body = Term.term
  
type concrete_operator = {
  name    : Symbols.fname;
  ty_vars : Type.tvar list;
  args    : Vars.var list;
  out_ty  : Type.ty;
  body    : body;
}

type Symbols.OpData.concrete_def += Val of concrete_operator

(*------------------------------------------------------------------*)
let pp_op_body fmt body = Fmt.pf fmt "%a" Term.pp body

let pp_concrete_operator fmt op =
  let pp_tyvars fmt tyvars =
    if tyvars = [] then () 
    else
      Fmt.pf fmt "[%a] " (Fmt.list ~sep:(Fmt.any " ") Type.pp_tvar) tyvars
  in
  let pp_args fmt args =
    if args = [] then () 
    else
      Fmt.pf fmt "(%a) " Vars.pp_typed_list args
  in

  Fmt.pf fmt "@[<hov 2>@[op %a %a%a: %a @]=@ @[%a@]@]"
    Symbols.OpData.pp_fname op.name
    pp_tyvars op.ty_vars
    pp_args op.args
    Type.pp op.out_ty
    pp_op_body op.body

(*------------------------------------------------------------------*)
let concrete_ftype (op : concrete_operator) : Type.ftype = 
  Type.mk_ftype op.ty_vars (List.map Vars.ty op.args) op.out_ty

let get_concrete_data (table : Symbols.table) (fsymb : Symbols.fname) : concrete_operator =
  match Symbols.OpData.get_data fsymb table with
  | { def = Concrete (Val data) } -> data
  | _ -> assert false

let is_concrete_operator (table : Symbols.table) (fsymb : Symbols.fname) : bool =
  match (Symbols.OpData.get_data fsymb table).def with
  | Concrete _ -> true
  | Abstract _ -> false

(*------------------------------------------------------------------*)
let is_system_indep (table : Symbols.table) (fsymb : Symbols.fname) : bool =
  match (Symbols.OpData.get_data fsymb table).def with
  | Concrete _ -> true
  (* for now, we only have system-independent operators so this check is 
     superfluous. *)
  | Abstract _ -> true

(*------------------------------------------------------------------*)
let unfold 
    (table  : Symbols.table)
    (_se    : SE.arbitrary)
    (opsymb : Symbols.fname)
    (tyargs : Type.ty list)
    (args   : Term.term list)
  : Term.term
  =
  let op = get_concrete_data table opsymb in

  (* apply type argument type variables *)
  let ts =
    List.fold_left2 Type.tsubst_add_tvar Type.tsubst_empty op.ty_vars tyargs
  in
  let op_args = List.map (Vars.tsubst ts) op.args in
  let op_body = Term.tsubst ts op.body in

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

