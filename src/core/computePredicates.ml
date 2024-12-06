module SE = SystemExpr
module LS = Library.Secrecy

(*------------------------------------------------------------------*)
type kind = Deduce | NotDeduce 

let predicate_to_kind table (p : Symbols.predicate) : kind =
  if p = LS.symb_deduce     table then Deduce    else
  if p = LS.symb_not_deduce table then NotDeduce
  else assert false

let kind_to_predicate table (k : kind) : Symbols.predicate =
  match k with
  | Deduce -> LS.symb_deduce     table
  | NotDeduce -> LS.symb_not_deduce table

(*------------------------------------------------------------------*)
type form = Equiv.pred_app

let is_computability (table:Symbols.table) (e:Equiv.form) : bool =
  LS.is_loaded table &&
  match e with
  | Atom (Pred pred_app) when
      pred_app.psymb = LS.symb_deduce table ||
      pred_app.psymb = LS.symb_not_deduce table -> true
  | _ -> false

let make
    (table     : Symbols.table) 
    (sk        : kind) 
    (se        : SE.fset) 
    ~(left_tys : Type.ty list)
    ~(right_ty : Type.ty)
    ~(left     : Term.terms) 
    ~(right    : Term.term) : form 
  =
  assert (List.length left_tys = List.length left);
  assert (LS.is_loaded table);
  let se = (se :> SE.arbitrary) in
  let left_tys, left =
    match left_tys, left with 
    | [], [] -> Type.tmessage, Term.mk_zero
    | _ ->  (Type.tuple left_tys, Term.mk_tuple left)
  in
  let psymb = kind_to_predicate table sk in
  Equiv.{ 
    psymb;
    ty_args    = [left_tys; right_ty];
    se_args    = [se];
    multi_args = [se, [left; right]];
    simpl_args = [];
  }

(*------------------------------------------------------------------*)
let from_global table (e:Equiv.form) : form =
  assert (is_computability table e);
  match e with 
  | Atom (Pred pa) -> pa
  | _ -> assert false

let to_global (pa:form) : Equiv.form =
  Equiv.Atom (Pred pa)

(*------------------------------------------------------------------*)
let kind table (pa:form) : kind = predicate_to_kind table pa.psymb

let system (pa:form) : SE.t =
  let se = List.hd pa.se_args in
  (* sanity check: the same system must be in the multi_args *)
  match pa.multi_args with 
  | [se', _] when SE.equal0 se se' -> se
  | _ -> assert false

(*------------------------------------------------------------------*)
let left (pa:form) : Term.term =
  match pa.multi_args with
  | [_, [u;_]] -> u
  | _ -> assert false 

let lefts (f : form) : Term.terms = 
  Term.destr_tuple_flatten (left f)

(*------------------------------------------------------------------*)
let right (pa:form) : Term.term =
  match pa.multi_args with
  | [_, [_;v]] -> v
  | _ -> assert false 

let rights (f : form) : Term.terms = 
  Term.destr_tuple_flatten (right f)

(*------------------------------------------------------------------*)
let update_lefts (left : Term.terms) (pa : form) : form =
  let right = right pa in
  let ty_left = List.map Term.ty left in
  let ty_right = Term.ty right in
  let left, ty_left =
    if List.length left = 0 then 
      [Term.mk_zero], [Type.tmessage]
    else
      left, ty_left
  in
  { pa with
    ty_args    = [Type.tuple ty_left; ty_right];
    multi_args = [system pa,
                  [Term.mk_tuple left; right]]
  }

let update_rights (right : Term.terms) (pa : form) : form =
  let left = left pa in
  let ty_left = Term.ty left in
  let ty_right = List.map Term.ty right in
  let right, ty_right =
    if List.length right = 0 then 
      [Term.mk_zero], [Type.tmessage]
    else
      right, ty_right
  in
  { pa with
    ty_args    = [ty_left; Type.tuple ty_right];
    multi_args = [system pa,
                  [left; Term.mk_tuple right]]
  }
