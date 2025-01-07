module SE = SystemExpr
module LS = Library.Secrecy

(*------------------------------------------------------------------*)

type side = Left | Right

let other (s:side) =
  match s with 
  | Left -> Right
  | Right -> Left
    
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

let term ~(side:side) (f:form) : Term.term =
  match side, f.multi_args with
  | Left, [_, [u;_]] -> u
  | Right, [_, [_; v]] -> v
  | _ -> assert false

let terms ~(side:side) (f:form) : Term.terms =
  Term.destr_tuple_flatten (term ~side f)

let left = term ~side:Left
let lefts = terms ~side:Left
let right = term ~side:Right
let rights = terms ~side:Right
    

(*------------------------------------------------------------------*)
let update_terms ~(side:side) (terms:Term.terms) (f:form) : form =
  let other_term = term ~side:(other side) f in
  let ty_terms = List.map Term.ty terms in
  let ty_other = Term.ty other_term in
  let terms, ty_terms =
    if terms = [] then
      [Term.mk_zero], [Type.tmessage]
    else
      terms, ty_terms
  in
  let term = Term.mk_tuple terms in
  let ty_term = Type.tuple ty_terms in
  let l, r, tyl, tyr =
    match side with
    | Left -> term, other_term, ty_term, ty_other
    | Right -> other_term, term, ty_other, ty_term
  in
  { f with
    ty_args = [tyl; tyr];
    multi_args = [system f, [l; r]]
  }


let update_lefts = update_terms ~side:Left

let update_rights = update_terms ~side:Right

