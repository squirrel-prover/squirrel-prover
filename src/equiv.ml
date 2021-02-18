(** Equivalence formulas.  *)

module Sv = Vars.Sv

(*------------------------------------------------------------------*)
(** {2 Equivalence} *)

type elem =
  | Formula of Term.formula
  | Message of Term.message

let pp_elem ppf = function
  | Formula t -> Term.pp ppf t
  | Message t -> Term.pp ppf t

let pi_term projection tm = Term.pi_term ~projection tm

let pi_elem s = function
  | Formula t -> Formula (pi_term s t)
  | Message t -> Message (pi_term s t)

(** Free variables of an [elem]. *)
let fv_elem = function
  | Formula e -> Term.fv e
  | Message e -> Term.fv e

(*------------------------------------------------------------------*)
type equiv = elem list

let pp_equiv ppf (l : equiv) =
  Fmt.pf ppf "%a"
    (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@ ") pp_elem)
    l

let pp_equiv_numbered ppf (l : equiv) =
  let max_i = List.length l - 1 in
  List.iteri (fun i elem ->
      if i < max_i then
        Fmt.pf ppf "%i: %a,@ " i pp_elem elem
      else
        Fmt.pf ppf "%i: %a" i pp_elem elem
    )
    l

let subst_equiv (subst : Term.subst) (f : equiv) : equiv =
List.map (function 
      | Formula f -> Formula (Term.subst subst f)
      | Message t -> Message (Term.subst subst t)
    ) f

(** Free variables of an [equiv]. *)
let fv_equiv e : Sv.t = 
  List.fold_left (fun sv elem -> 
      Sv.union sv (fv_elem elem)
    ) Sv.empty e

(*------------------------------------------------------------------*)
(** {2 Equivalence atoms} *)

type atom = 
  | Equiv of equiv
  (** Equiv u corresponds to (u)^left ~ (u)^right *)

  | Reach of Term.formula
  (** Reach(φ) corresponds to (φ)^left ~ ⊤ ∧ (φ)^right ~ ⊤ *)

let pp_atom fmt = function
  | Equiv e -> pp_equiv fmt e
  | Reach f -> Fmt.pf fmt "@[[%a]@]" Term.pp f

let subst_atom (subst : Term.subst) (a : atom) : atom = 
  match a with
  | Equiv e -> Equiv (subst_equiv subst e)
  | Reach f -> Reach (Term.subst subst f)

(** Free variables of an [atom]. *)
let fv_atom = function
  | Equiv e -> fv_equiv e
  | Reach f -> Term.fv f

(*------------------------------------------------------------------*)
(** {2 Equivalence formulas} *)
(** We only support a small fragment for now *)

type form = 
  | Atom of atom
  | Impl of (form * form)

let rec pp_form fmt = function
  | Atom at -> pp_atom fmt at
  | Impl (f0, f) -> 
    Fmt.pf fmt "%a -> %a" pp_form f0 pp_form f

let rec subst_form subst (f : form) = 
  match f with
  | Atom at -> Atom (subst_atom subst at)
  | Impl (f0, f) -> Impl (subst_form subst f0, subst_form subst f)

(** Free variables of an [atom]. *)
let rec fv_form = function
  | Atom at -> fv_atom at
  | Impl (f,f0) -> Sv.union (fv_form f) (fv_form f0)
