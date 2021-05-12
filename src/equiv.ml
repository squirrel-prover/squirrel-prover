open Utils

(** Equivalence formulas.  *)

module Sv = Vars.Sv

(*------------------------------------------------------------------*)
(** {2 Equivalence} *)

let pi_term projection tm = Term.pi_term ~projection tm

(*------------------------------------------------------------------*)
type equiv = Term.message list

let pp_equiv ppf (l : equiv) =
  Fmt.pf ppf "@[%a@]"
    (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@ ") Term.pp)
    l

let pp_equiv_numbered ppf (l : equiv) =
  let max_i = List.length l - 1 in
  List.iteri (fun i elem ->
      if i < max_i then
        Fmt.pf ppf "%i: %a,@ " i Term.pp elem
      else
        Fmt.pf ppf "%i: %a" i Term.pp elem
    )
    l

let subst_equiv (subst : Term.subst) (e : equiv) : equiv =
  List.map (Term.subst subst) e

(** Free variables of an [equiv]. *)
let fv_equiv e : Sv.t = 
  List.fold_left (fun sv elem -> 
      Sv.union sv (Term.fv elem)
    ) Sv.empty e

(*------------------------------------------------------------------*)
(** {2 Equivalence atoms} *)

type atom = 
  | Equiv of equiv
  (** Equiv u corresponds to (u)^left ~ (u)^right *)

  | Reach of Term.message
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
  | ForAll of Vars.evar list * form
  | Atom   of atom
  | Impl   of (form * form)

let rec pp fmt = function
  | Atom at -> pp_atom fmt at
  | Impl (f0, f) -> 
    Fmt.pf fmt "@[<v 2>%a ->@ %a@]" pp f0 pp f
  | ForAll (vs, f) -> 
    Fmt.pf fmt "@[<v 2>forall (@[%a@]),@ %a@]"
      Vars.pp_typed_list vs pp f

let mk_forall evs f = match evs, f with
  | [], _ -> f
  | _, ForAll (evs', f) -> ForAll (evs @ evs', f)
  | _, _ -> ForAll (evs, f)

let mk_reach_atom f = Atom (Reach f)

(*------------------------------------------------------------------*)

(** Free variables. *)
let rec fv = function
  | Atom at -> fv_atom at
  | Impl (f,f0) -> Sv.union (fv f) (fv f0)
  | ForAll (evs, b) -> Sv.diff (fv b) (Sv.of_list evs)

let rec subst s (f : form) = 
  if s = [] ||
     (Term.is_var_subst s && 
      Sv.disjoint (Term.subst_support s) (fv f))
  then f
  else 
    match f with
    | Atom at -> Atom (subst_atom s at)

    | Impl (f0, f) -> Impl (subst s f0, subst s f)

    | ForAll ([], f) -> subst s f
    | ForAll (v :: evs, b) -> 
      let v, s = Term.subst_binding v s in
      let f = subst s (ForAll (evs,f)) in
      mk_forall [v] f


(*------------------------------------------------------------------*)
(** {2 Matching} *)
module Match : Term.MatchS with type t = form = struct 
  module TMatch = Term.Match

  (* We include Term.Match, and redefine any necessary function *)
  include TMatch

  type t = form

  let try_match (t : form) pat = 
    match t with
    | Atom (Reach f) -> TMatch.try_match f pat
    | _ -> `NoMatch

  let rec find_map :
    type b. many:bool -> 
    Vars.env -> form -> b Term.pat -> 
    (b Term.term -> Vars.evars -> mv -> b Term.term) -> 
    form option
    = fun ~many env e p func ->
      match e with
      | Atom (Reach f) -> 
        omap (fun x -> Atom (Reach (x))) (TMatch.find_map ~many env f p func)
      | Atom (Equiv e) -> 
        let found = ref false in

        let e = List.fold_left (fun acc f ->
            if not !found || many then
              match TMatch.find_map ~many env f p func with
              | None -> f :: acc
              | Some f -> found := true; f :: acc
            else f :: acc
          ) [] e
        in
        let e = List.rev e in

        if !found then Some (Atom (Equiv e)) else None

      | Impl (e1, e2) -> 
        let found, e1 = 
          match find_map ~many env e1 p func with
          | Some e1 -> true, e1
          | None -> false, e1 
        in
        
        let found, e2 = 
          if not found || many then
            match find_map ~many env e2 p func with
            | Some e2 -> true, e2
            | None -> false, e2
          else found, e2
        in
        if found then Some (Impl (e1, e2)) else None

      | ForAll (vs, e) -> None  (* FIXME: match under binders *)

end
