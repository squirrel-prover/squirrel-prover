module L    = Location
module SE   = SystemExpr
module Sv   = Vars.Sv

(*------------------------------------------------------------------*)
(** See `.mli` *)
type rw_kind = LocalEq | GlobalEq

(*------------------------------------------------------------------*)
(** See `.mli` *)
type rw_rule = {
  rw_params : Params.t;
  rw_system : SE.t;                  
  rw_vars   : Vars.tagged_vars;      
  rw_conds  : Term.term list; 
  rw_rw     : Term.term * Term.term; 
  rw_kind   : rw_kind;
  rw_bound  : Concrete.bound;
}

let pp_rw_rule ppe fmt (rw : rw_rule) =
  let pp_vars fmt vars = 
    if vars = [] then () else
      Fmt.pf fmt "%a " Vars.pp_typed_tagged_list vars
  in
  let pp_conds fmt conds =
    if conds = [] then () else
      Fmt.pf fmt " when %a" (Fmt.list (Term._pp ppe)) conds
  in
  
  let src, dst = rw.rw_rw in
  Fmt.pf fmt "%a%a: %a -> %a%a"
    Params.pp rw.rw_params
    pp_vars rw.rw_vars
    (Term._pp ppe) src Term.pp dst
    pp_conds rw.rw_conds

(*------------------------------------------------------------------*)
(** Check that the rule is correct. *)
let check_rule (rule : rw_rule) : unit =
  let l, _r = rule.rw_rw in
  let rule_vars = Sv.of_list (List.map fst rule.rw_vars) in
  
  if not (Vars.Sv.subset rule_vars (Term.fv l)) then
    Tactics.hard_failure Tactics.BadRewriteRule;
  ()

(*------------------------------------------------------------------*)
(** Make a rewrite rule from a pattern *)
let pat_to_rw_rule ?loc 
    ~(destr_eq  : Term.term -> (Term.term * Term.term) option)
    ~(destr_not : Term.term -> (            Term.term) option)
    (system    : SE.arbitrary) 
    (rw_kind   : rw_kind)
    (dir       : [< `LeftToRight | `RightToLeft ])
    (p         : (Term.term * Concrete.bound) Term.pat)
  : rw_rule 
  =
  let _ = loc in                (* unused *)
  let formula, rw_bound = p.pat_term in
  let subs, f = Term.decompose_impls_last formula in

  let e = match destr_eq f with
    | Some (t1, t2) -> t1,t2
    | _ ->
        match destr_not f with
        | Some neg_f -> neg_f, Term.mk_false
        | None       ->     f, Term.mk_true
  in

  let e = match dir with
    | `LeftToRight -> e
    | `RightToLeft ->
      let t1,t2 = e in
      t2,t1
  in

  let rule = {
    rw_params = p.pat_params;
    rw_system = system;
    rw_vars   = p.pat_vars;
    rw_conds  = subs;
    rw_rw     = e;
    rw_kind;
    rw_bound;
  } in
  
  (* We check that the rule is valid *)
  check_rule rule;

  rule

(*------------------------------------------------------------------*)
let simple_rw_rule
    ?(params = Params.empty) ?(vars = []) ?(conds = [])
    (system  : SE.arbitrary) 
    ~(left : Term.t) ~(right : Term.t)
  : rw_rule 
  =
  let rule = {
    rw_params = params;
    rw_system = system;
    rw_vars   = vars;
    rw_conds  = conds;
    rw_rw     = (left,right);
    rw_kind   = GlobalEq;
    rw_bound = Glob;
    (* FIXME: we want to say that the rule is exact. *)
  } 
  in
  
  (* We check that the rule is valid *)
  check_rule rule;

  rule
