include Library.Real

let zero table = mk_zero table

let of_int (table : Symbols.table ) (n : int) : Term.term =
  mk_of_int table (Term.mk_int (Z.of_int n))

let is_zero  (table : Symbols.table) (r : Term.term)  : bool =
  Term.equal r (Library.Real.mk_zero table)
  || Term.equal r (of_int table 0)

let is_one (table : Symbols.table) (r : Term.term)  : bool =
  Term.equal r (of_int  table 1)

let rec not_is_zero (table : Symbols.table) (r : Term.term) : bool =
  match r with
  | _ when is_one table r -> true
  | Term.App(Term.Fun(f,_),[Term.Int n])
    when f = fs_of_int  -> Z.(n <> zero)
  | Term.App(Term.Fun(f,_),[a;b])
    when f = fs_div table -> (not_is_zero table a) && (not_is_zero table b)
  | Term.App(Term.Fun(f,_),[a])
    when f = fs_inv table -> (not_is_zero table a)
  | _ -> false

let rec ge_zero (table : Symbols.table) (r : Term.term) : bool =
  match r with
  | _ when is_zero table r ->  true
  | _ when is_one table r ->  true
  | Term.App(Term.Fun(f,_),[Term.Int n])
    when f = fs_of_int  -> Z.(n >= zero)
  | Term.App(Term.Fun(f,_),[a;b])
    when f = fs_div table ->
    ge_zero table a && ge_zero table b && (not_is_zero table b)
  | Term.App(Term.Fun(f,_),[a])
    when f = fs_inv table ->
    ge_zero table a && (not_is_zero table a)
  | _ -> false

let mk_opp (table : Symbols.table) (r : Term.term) : Term.term =
  match r with
  | _ when is_zero table r -> r
  | Term.App (Term.Fun(f,_),[r]) when f = fs_opp table -> r
  | _ -> mk_opp table r

(*------------------------------------------------------------------*)
let mk_minus
    ?(simpl=true) (table : Symbols.table) 
    (a : Term.term) (b : Term.term)
  : Term.term 
  =
  if simpl && is_zero table b then a else Library.Real.mk_minus table a b

(*------------------------------------------------------------------*)
let mk_add
    ?(simpl=true) (table : Symbols.table) 
    (a : Term.term) (b : Term.term)
  : Term.term 
  =
  if simpl then
    if is_zero table b then a
    else if is_zero table a then b
    else Library.Real.mk_add table a b
  else Library.Real.mk_add table a b

(*------------------------------------------------------------------*)
(** Compute [sum_v t] ([vars] must be [finite]) 
    which sums the all values of [t] for any value of [v]. *)
let mk_sum_tpred
    (table : Symbols.table) (var : Vars.var) (t : Term.t) 
  =
  Library.Real.mk_sum table
    (Term.mk_lambda [var] Term.mk_true) (* [λ _. ⊤] *)
    (Term.mk_lambda [var] t)            (* [λ v. ⊤] *)

(*------------------------------------------------------------------*)
(** Compute [sum_vars t], represented by [sum_v1 … sum_vN t]
    when [vars = v1, …, vN].
    [vars] must be [finite].  *)
let mk_sums_tpred
    (table : Symbols.table) 
    (vars : Vars.var list) (t : Term.t) 
  =
  List.fold_left (fun t var -> mk_sum_tpred table var t) t vars 
