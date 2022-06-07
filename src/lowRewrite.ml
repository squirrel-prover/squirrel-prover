module L    = Location
module SE   = SystemExpr
module Sv   = Vars.Sv

(*------------------------------------------------------------------*)
(** A rewrite rule.
    Invariant: if
    [{ rw_tyvars = tyvars; rw_vars = sv; rw_conds = φ; rw_rw = (l,r); }]
    is a rewrite rule, then:
    - sv ⊆ FV(l) *)
type rw_rule = {
  rw_tyvars : Type.tvars;            (** type variables *)
  rw_system : SE.t;                  (** systems the rule applies to *)
  rw_vars   : Vars.Sv.t;             (** term variables *)
  rw_conds  : Term.term list;        (** premises *)
  rw_rw     : Term.term * Term.term; (** pair (source, destination) *)
}

let pp_rw_rule fmt (rw : rw_rule) =
  let pp_tys fmt tys = 
    if tys = [] then () else
      Fmt.pf fmt "[%a] " (Fmt.list Type.pp_tvar) tys
  in
  let pp_vars fmt vars = 
    if Vars.Sv.is_empty vars then () else
      Fmt.pf fmt "%a " Vars.pp_typed_list (Vars.Sv.elements vars)
  in
  let pp_conds fmt conds =
    if conds = [] then () else
      Fmt.pf fmt " when %a" (Fmt.list Term.pp) conds
  in
  
  let src, dst = rw.rw_rw in
  Fmt.pf fmt "%a%a: %a -> %a%a"
    pp_tys rw.rw_tyvars
    pp_vars rw.rw_vars
    Term.pp src Term.pp dst
    pp_conds rw.rw_conds

(*------------------------------------------------------------------*)
(** Check that the rule is correct. *)
let check_rule (rule : rw_rule) : unit =
  let l, r = rule.rw_rw in

  if not (Vars.Sv.subset rule.rw_vars (Term.fv l)) then
    Tactics.hard_failure Tactics.BadRewriteRule;
  ()

(** Make a rewrite rule from a formula *)
let pat_to_rw_rule ?loc 
    ~(destr_eq : Term.term -> (Term.term * Term.term) option)
    (system    : SE.arbitrary) 
    (dir       : [< `LeftToRight | `RightToLeft ])
    (p         : Term.term Term.pat) 
  : rw_rule 
  =
  let subs, f = Term.decompose_impls_last p.pat_term in

  let e = match destr_eq f with
    | Some (t1, t2) -> t1,t2
    | _ -> Tactics.hard_failure ?loc (Tactics.Failure "not an equality")
  in

  let e = match dir with
    | `LeftToRight -> e
    | `RightToLeft ->
      let t1,t2 = e in
      t2,t1
  in

  let rule = {
    rw_tyvars = p.pat_tyvars;
    rw_system = system;
    rw_vars   = p.pat_vars;
    rw_conds  = subs;
    rw_rw     = e;
  } in

  (* We check that the rule is valid *)
  check_rule rule;

  rule