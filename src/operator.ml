open Utils

module SE = SystemExpr

(*------------------------------------------------------------------*)
(** operator body *)
type body = Term.term

type[@warning "-37"] op_body =
  | SingleDef of body                      (** same for all systems *)
  
  | ManyDefs  of (System.Single.t * body) list (** system by system *)
  (* TODO: unused for now *)

type operator = {
  name    : string;
  ty_vars : Type.tvar list;
  args    : Vars.var list;
  out_ty  : Type.ty;
  body    : op_body;
}

type Symbols.data += Operator of operator

(*------------------------------------------------------------------*)
let pp_op_body fmt body =
  match body with
  | SingleDef t -> Fmt.pf fmt "%a" Term.pp t
  | ManyDefs  l -> 
    Fmt.pf fmt "@[<v 0>%a@]"
      (Fmt.list (Fmt.pair ~sep:Fmt.comma System.Single.pp Term.pp)) l

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
  let body = SingleDef body in
  { name; ty_vars; args; out_ty; body }

let ftype (op : operator) : Type.ftype = 
  Type.mk_ftype op.ty_vars (List.map Vars.ty op.args) op.out_ty

let get_body (system : 'a SystemExpr.expr) (op_body : op_body) : body =
  match op_body with
    | SingleDef body -> body
    | ManyDefs defs -> assert false (* TODO *)

let is_operator (table : Symbols.table) (fsymb : Term.fsymb) : bool =
  match Symbols.Function.get_data fsymb table with
  | Operator op -> true
  | _ -> false

let unfold 
    (table  : Symbols.table)
    (se     : SE.arbitrary)
    (opsymb : Term.fsymb)
    (args   : Term.term list)
  : Term.term
  =
  let op = 
    match Symbols.Function.get_data opsymb table with
    | Operator op -> op
    | _ -> assert false
  in
  let body = get_body se op.body in

  let subst = 
    List.map2 (fun x y -> 
        Term.ESubst (Term.mk_var x,y)
      ) op.args args
  in
  Term.subst subst body
