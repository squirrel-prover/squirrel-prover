(** A rewrite rule is a tuple: 
    (type variables, term variables, premisses, left term, right term)
    Invariant: if (tyvars,sv,φ,l,r) is a rewrite rule, then
    - sv ⊆ FV(l)
    - ((FV(r) ∪ FV(φ)) ∩ sv) ⊆ FV(l) *)
type 'a rw_rule = 
  Type.tvars * Vars.Sv.t * Term.message list * 'a Term.term * 'a Term.term

type rw_erule = Type.tvars * Vars.Sv.t * Term.message list * Term.esubst

(*------------------------------------------------------------------*)
(** Check that the rule is correct. *)
let check_erule ((_, sv, h, Term.ESubst (l,r)) : rw_erule) : unit =
  let fvl, fvr = Term.fv l, Term.fv r in
  let sh = List.fold_left (fun sh h ->
      Vars.Sv.union sh (Term.fv h)
    ) Vars.Sv.empty h
  in

  if not (Vars.Sv.subset sv fvl) || 
     not (Vars.Sv.subset (Vars.Sv.inter (Vars.Sv.union fvr sh) sv) fvl) then 
    Tactics.hard_failure Tactics.BadRewriteRule;
  ()

(*------------------------------------------------------------------*)
exception NoRW

let rewrite_head : 
  rw_erule -> Term.message -> Term.message * Term.message list =
  fun rule t ->
  let tyvars, vars, subs, rule_subst = rule in
  let (l, r) : Term.message * Term.message = 
    match rule_subst with
    | Term.ESubst (l, r) -> 
      match Type.equalk_w (Term.kind t) (Term.kind l) with
      | Some Type.Type_eq -> l, r
      | None -> raise NoRW
  in

  let pat = 
    Term.{ pat_tyvars = tyvars; pat_vars = vars; pat_term = l; } 
  in

  let mv = 
    match Term.Match.try_match t pat with
    | `FreeTyv | `NoMatch -> raise NoRW
    | `Match mv -> mv
  in
  let subst = Term.Match.to_subst mv in
  let r = Term.subst subst r in
  let subs = List.map (Term.subst subst) subs in
  r, subs

let rewrite_head : type a.
  rw_erule -> a Term.term -> (a Term.term * Term.message list) option =
  fun rule t ->
  match Type.equalk_w Type.KMessage (Term.kind t) with
  | None -> None
  | Some Type.Type_eq ->
    try Some (rewrite_head rule t) with NoRW -> None


