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

  Fmt.pf fmt "@[<hov 2>@[op %s %a%a: %a @]=@ @[%a@]@]"
    op.name
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
    (args   : Term.term list)
  : [`FreeTyv | `Ok of Term.term]
  =
  let op = 
    match Symbols.Function.get_data opsymb table with
    | Operator op -> op
    | _ -> assert false
  in

  (* create a new ty_env *)
  let ty_env = Type.Infer.mk_env () in

  (* refresh type variables *)
  let _, ts = Type.Infer.open_tvars ty_env op.ty_vars in
  let op_args = List.map (Vars.tsubst ts) op.args in
  let op_body =
    match op.body with Single body -> Term.tsubst ts body
  in

  let args1, args2 = List.takedrop (List.length op_args) args in

  let subst = 
    List.map2 (fun x t ->       (* add types information to [ty_env] *)
        let _ : [`Ok | `Fail] =
          Type.Infer.unify_leq ty_env (Term.ty t) (Vars.ty x)
        in
        
        Term.ESubst (Term.mk_var x,t)
      ) op_args args1
  in
  let term = Term.mk_app (Term.subst subst op_body) args2 in
  
  
  if not (Type.Infer.is_closed ty_env) then `FreeTyv
  else
    let tysubst = Type.Infer.close ty_env in
    `Ok (Term.tsubst tysubst term)
  
