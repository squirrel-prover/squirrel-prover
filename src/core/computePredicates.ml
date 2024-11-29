module SE = SystemExpr
module LS = Library.Secrecy

(*------------------------------------------------------------------*)
type kind = Deduce | NotDeduce 

type form = kind * Equiv.pred_app

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
  let pa = 
    Equiv.{ psymb = (match sk with
        | Deduce -> LS.symb_deduce table
        | NotDeduce -> LS.symb_not_deduce table);
        ty_args = [left_tys; right_ty];
        se_args = [se];
        multi_args = [se, [left; right]];
        simpl_args = []}
  in
  sk, pa

let from_global
    (table:Symbols.table) (e:Equiv.form) : form 
  =
  match e with 
  | Atom (Pred pa) -> 
    let sk = 
      if pa.psymb = LS.symb_deduce table then Deduce
      else if pa.psymb = LS.symb_not_deduce table then NotDeduce
      else assert false
    in
    (sk, pa)
  | _ -> assert false

let to_global (_, pa:form) : Equiv.form =
  Equiv.Atom (Pred pa)

(*------------------------------------------------------------------*)
let kind (sk, _:form) : kind =
  sk

let system (_, pa:form) : SE.t =
  let se = List.hd pa.se_args in
  (* sanity check: the same system must be in the multi_args *)
  match pa.multi_args with 
  | [se', _] when SE.equal0 se se' -> se
  | _ -> assert false

let left0 (_, pa:form) : Term.term =
  match pa.multi_args with
  | [_, [u;_]] -> u
  | _ -> assert false 

let left (_, pa:form) : Term.terms =
  match pa.multi_args with
  | [_, [u;_]] -> Term.destr_tuple_flatten u
  | _ -> assert false 

let right (_, pa:form) : Term.term =
  match pa.multi_args with
  | [_, [_;v]] -> v
  | _ -> assert false 

let update_left
    (left : Term.terms) (sk, pa : form) : form
  =
  let right = right (sk, pa) in
  let ty_left = List.map Term.ty left in
  let ty_right = Term.ty right in
  let left, ty_left =
    if List.length left = 0 then 
      [Term.mk_zero], [Type.tmessage]
    else
      left, ty_left
  in
  ( sk,
    {pa with
     ty_args    = [Type.tuple ty_left; ty_right];
     multi_args = [system (sk, pa),
                   [Term.mk_tuple left; right]]
    } )

let update_right
    (right : Term.terms) (sk, pa : form) : form
  =
  let left = left0 (sk,pa) in
  let ty_left = Term.ty left in
  let ty_right = List.map Term.ty right in
  let right, ty_right =
    if List.length right = 0 then 
      [Term.mk_zero], [Type.tmessage]
    else
      right, ty_right
  in
  ( sk,
    {pa with
     ty_args    = [ty_left; Type.tuple ty_right];
     multi_args = [system (sk, pa),
                   [left; Term.mk_tuple right]]
    } )
