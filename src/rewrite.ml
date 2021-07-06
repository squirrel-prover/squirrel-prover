module SE = SystemExpr

(*------------------------------------------------------------------*)
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

(** Make a rewrite rule from a formula *)
let pat_to_rw_erule ?loc dir (p : Term.message Match.pat) : rw_erule = 
  let subs, f = Term.decompose_impls_last p.pat_term in

  let e = match f with
    | Term.Atom (`Message   (`Eq, t1, t2)) -> Term.ESubst (t1,t2)
    | Term.Atom (`Timestamp (`Eq, t1, t2)) -> Term.ESubst (t1,t2)
    | Term.Atom (`Index     (`Eq, t1, t2)) -> 
      Term.ESubst (Term.mk_var t1,Term.mk_var t2)
    | _ -> Tactics.hard_failure ?loc (Tactics.Failure "not an equality") 
  in

  let e = match dir with
    | `LeftToRight -> e
    | `RightToLeft -> 
      let Term.ESubst (t1,t2) = e in
      Term.ESubst (t2,t1)
  in

  let rule = p.pat_tyvars, p.pat_vars, subs, e in

  (* We check that the rule is valid *)
  check_erule rule;

  rule

(*------------------------------------------------------------------*)
exception NoRW

let rewrite_head 
    (table  : Symbols.table)
    (system : SE.t)
    (rule   : rw_erule)
    (t      : Term.message) : Term.message * Term.message list
  =
  let tyvars, vars, subs, rule_subst = rule in
  let (l, r) : Term.message * Term.message = 
    match rule_subst with
    | Term.ESubst (l, r) -> 
      match Type.equalk_w (Term.kind t) (Term.kind l) with
      | Some Type.Type_eq -> l, r
      | None -> raise NoRW
  in

  let pat = 
    Match.{ pat_tyvars = tyvars; pat_vars = vars; pat_term = l; } 
  in

  let mv = 
    match Match.T.try_match table system t pat with
    | FreeTyv | NoMatch _ -> raise NoRW
    | Match mv -> mv
  in
  let subst = Match.Mvar.to_subst ~mode:`Match mv in
  let r = Term.subst subst r in
  let subs = List.map (Term.subst subst) subs in
  r, subs

let rewrite_head : type a.
  Symbols.table ->
  SE.t ->
  rw_erule -> a Term.term -> 
  (a Term.term * Term.message list) option
  =
  fun table system rule t ->
  match Type.equalk_w Type.KMessage (Term.kind t) with
  | None -> None
  | Some Type.Type_eq ->
    try Some (rewrite_head table system rule t) with NoRW -> None


