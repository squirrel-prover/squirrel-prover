(** Tactics exploiting a name's freshness. *)
open Squirrelcore

open Utils
    
module NO = NameOccs
module Name = NO.Name
                
module TS = TraceSequent
module ES = EquivSequent

module Hyps = TS.LocalHyps

module MP = Match.Pos
module Sp = Match.Pos.Sp

open LowTactics

(*------------------------------------------------------------------*)
let soft_failure = Tactics.soft_failure
let hard_failure = Tactics.hard_failure

type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
(** for now, `fresh` has only one named optional arguments *)
let p_fresh_arg (nargs : Args.named_args) : bool =
  match nargs with
  | [Args.NArg L.{ pl_desc = "precise_ts" }] -> true

  | Args.NList (l,_) :: _ 
  | Args.NArg  l     :: _ ->
    hard_failure ~loc:(L.loc l) (Failure "unknown argument")

  | [] -> false

(*------------------------------------------------------------------*)
(** {2 Library: used in trace and equiv fresh} *)

(** Look for occurrences using [NameOccs].
    A [(unit,unit) NO.f_fold_occs] function, for use with [NO.occurrence_goals].
    Looks for occurrences of [n] in [t]:
    - if [t] is [n]: returns the occurrence
    - otherwise: asks to be called recursively on subterms.
    Do not uses an accumulator, so returns an empty unit list. *)
let get_bad_occs
    (env : Env.t)
    (n   : Name.t) 
    (retry_on_subterms : unit -> NO.n_occs * NO.empty_occs)
    (rec_call_on_subterms : 
       (fv   : Vars.vars ->
        cond : Term.terms ->
        p    : MP.pos ->
        info : NO.expand_info ->
        st   : Term.term -> 
        Term.term ->
        NO.n_occs * NO.empty_occs))
    ~(info : NO.expand_info)
    ~(fv   : Vars.vars)
    ~(cond : Term.terms)
    ~(p    : MP.pos)
    ~(st   : Term.term)
    (t     : Term.term) 
  : NO.n_occs * NO.empty_occs
  =
  let _ = p in (* unused for now *)

  (* handles a few cases, using [rec_call_on_subterm] for rec calls,
     and calls [retry_on_subterm] for the rest *)
  (* only use this rec_call shorthand if the parameters don't change! *)
  let rec_call = (* rec call on a list *)
    List.flattensplitmap (rec_call_on_subterms ~fv ~cond ~p ~info ~st)
  in

  let env =
    Env.update ~vars:(Vars.add_vars (Vars.Tag.global_vars ~const:true fv) env.vars) env
  in
  match t with
  (* for freshness, we can ignore **constant** subterms *)
  | _ when HighTerm.is_constant env t -> retry_on_subterms ()

  | Var v ->
    soft_failure
      (Failure (Fmt.str "terms contain a non-constant variable: %a" Vars.pp v))

  | Name (nn, nn_args) when nn.s_symb = n.Name.symb.s_symb ->
    let occs, _ = rec_call nn_args in    
    (NO.mk_nocc (Name.of_term t) n fv cond (fst info) st) :: occs, []

  | _ -> retry_on_subterms ()


(*------------------------------------------------------------------*)
(** {2 Trace fresh tactic} *)

(** Computes parameters for the fresh trace tactic:
    returns n, t such that hyp is n = t or t = n
    (looks under macros if possible *)
let fresh_trace_param
    ~(hyp_loc : L.t) 
    (info     : NO.expand_info) 
    (hyp      : Term.term)
    (s        : TS.sequent)
  : Name.t * Term.term
  =
  let _, contx = info in
  let table = contx.table in
  let m1, m2 = match TS.Reduce.destr_eq s Equiv.Local_t hyp with
    | Some (u, v) -> (u,v)
    | None -> 
      soft_failure ~loc:hyp_loc
        (Tactics.Failure "can only be applied on an equality hypothesis")
  in
  let em1 = NO.expand_macro_check_all info m1 in
  let em2 = NO.expand_macro_check_all info m2 in
  let n, t = match em1, em2 with
    | (Name _ as ns), _ -> (Name.of_term ns, em2)
    | _, (Name _ as ns) -> (Name.of_term ns, em1)
    | _ ->
      soft_failure ~loc:hyp_loc
        (Tactics.Failure "can only be applied on an hypothesis of \
                          the form t=n or n=t")
  in
  let ty = n.Name.symb.s_typ in
  if not Symbols.TyInfo.(check_bty_info table ty Symbols.Large) then
    Tactics.soft_failure
      (Failure "the type of this term is not [large]");

  (n, t)


(** Applies fresh to the trace sequent s and hypothesis m:
    returns the list of subgoals with the added hyp that there is a collision *)
let fresh_trace
    (opt_args : Args.named_args) (m : lsymb) (s : TS.sequent) 
  : TS.sequent list 
  =
  let use_path_cond = p_fresh_arg opt_args in

  let _, hyp = Hyps.by_name m s in
  try
    let contx = TS.mk_trace_cntxt s in
    let env = TS.env s in
    let (n, t) =
      fresh_trace_param ~hyp_loc:(L.loc m) (NO.EI_direct, contx) hyp s
    in

    let pp_n ppf () = Fmt.pf ppf "%a" Name.pp n in
    let get_bad = get_bad_occs env n in
   
    Printer.pr "Freshness of %a:@; @[<v 0>" pp_n ();
    let phis =
      NO.name_occurrence_formulas ~mode:Iter.Const ~use_path_cond ~pp_ns:(Some pp_n)
        get_bad contx env (t :: n.args)
    in
    Printer.pr "@]@;";

    let g = TS.goal s in
    List.map
      (fun phi ->
         TS.set_goal (Term.mk_impl ~simpl:false phi g) s)
      phis
  with
  | SE.(Error Expected_fset) ->
    soft_failure Underspecified_system


(** fresh trace tactic *)
let fresh_trace_tac (args : TacticsArgs.parser_args) : LowTactics.ttac =
  match args with
  | [Args.Fresh (opt_args, Args.FreshHyp hyp)] -> 
    TraceLT.wrap_fail (fresh_trace opt_args hyp)

  | _ -> bad_args ()


(*------------------------------------------------------------------*)
(** {2 Fresh equiv tactic} *)

(** Constructs the formula expressing the freshness of the projection
   by [proj] of [t] in the projection of the [biframe], provided it is
   a name member of a large type *)
let equiv_fresh_phi_proj
    ~(use_path_cond : bool)
    (loc            : L.t)
    (contx          : Constr.trace_cntxt)
    (venv           : Vars.env)
    (t              : Term.term)
    (biframe        : Term.terms)
    (proj           : Term.proj) 
  : Term.terms
  =
  let table = contx.table in
  let system = SE.project [proj] contx.system in
  let contx = { contx with system } in
  let env = Env.init ~table ~system:(SE.reachability_context system) ~vars:venv () in
  let info = (NO.EI_direct, contx) in

  let t = NO.expand_macro_check_all info (Term.project1 proj t) in
  let n : Name.t = 
    match t with
    | Name _ -> Name.of_term t
    | _ -> soft_failure ~loc
             (Tactics.Failure "Can only be applied to diff(n_L, n_R).")
  in

  let ty = n.Name.symb.s_typ in
  if not Symbols.TyInfo.(check_bty_info table ty Symbols.Large) then
    Tactics.soft_failure ~loc
      (Tactics.Failure "the type of this term is not [large]");

  (* [frame] is the projection of [biframe] over [proj] *)
  let frame = List.map (Term.project1 proj) biframe in
  let pp_n ppf () = Fmt.pf ppf "%a" Name.pp n in

  let get_bad : (unit, unit) NO.f_fold_occs = get_bad_occs env n in

  let phi : Term.terms =
    NO.name_occurrence_formulas
      ~mode:Iter.Const ~use_path_cond ~negate:true ~pp_ns:(Some pp_n)
      get_bad contx env (frame @ n.args)
  in

  (* We do not remove duplicates here, as we already do that on
     occurrences. 
     Later, we remove duplicates between the left and
     right occurrences [phi_l] and [phi_r]. *)
  phi

(*------------------------------------------------------------------*)
(** Constructs the sequent where goal [i], when of the form [diff(n_l, n_r)],
    is replaced with [if phi then zero else diff(n_l, n_r)],
    where [phi] expresses the freshness of [n_l] on the left, and [n_r] on 
    the right *)
let fresh_equiv
    (opt_args : Args.named_args) (i : int L.located) (s : ES.sequent) 
  : ES.sequents 
  =
  let use_path_cond = p_fresh_arg opt_args in

  let contx = ES.mk_pair_trace_cntxt s in
  let env = ES.vars s in
  let loc = L.loc i in

  let proj_l, proj_r = ES.get_system_pair_projs s in

  let before, t, after = split_equiv_goal i s in
  let biframe = List.rev_append before after in
  
  (* compute the freshness conditions *)
  Printer.pr "@[<v 0>Freshness on the left side:@; @[<v 0>";
  let phi_l = equiv_fresh_phi_proj ~use_path_cond loc contx env t biframe proj_l in

  Printer.pr "@]@,Freshness on the right side:@; @[<v 0>";
  let phi_r = equiv_fresh_phi_proj ~use_path_cond loc contx env t biframe proj_r in

  Printer.pr "@]@]@;";

  (* Removing duplicates. We already did that for occurrences, but
     only within [phi_l] and [phi_r], not across both *)
  let cstate = Reduction.mk_cstate contx.table in
  let phis =
    List.remove_duplicate (Reduction.conv cstate) (phi_l @ phi_r)
  in

  let phi = Term.mk_ands ~simpl:true phis in
  let new_biframe = List.rev_append before after in
  [ES.set_reach_goal phi s;
   ES.set_equiv_goal new_biframe s]


(** fresh equiv tactic *)
let fresh_equiv_tac (args : TacticsArgs.parser_args) : LowTactics.etac = 
  match args with
  | [Args.Fresh (opt_args, Args.FreshInt i)] -> 
    EquivLT.wrap_fail (fresh_equiv opt_args i)

  | _ -> bad_args ()


(*------------------------------------------------------------------*)
let () =
  T.register_general "fresh"
    ~tactic_help:{
      general_help = "Exploit the freshness of a name.";
      detailed_help =
        "Local sequent:\n\
         Given a message equality M of the form t=n, \
         add an hypothesis expressing that n is a subterm of t.\
         This condition checks that all occurences of the same name \
         in other actions cannot have happened before this action.\n\
         Global sequent:\n\
         Removes a name if fresh: \
         replace a name n by the term 'if fresh(n) then zero \
         else n, where fresh(n) captures the fact that this specific \
         instance of the name cannot have been produced by another \
         action.";
      usages_sorts = [Sort String; Sort Int];
      tactic_group=Structural }
    ~pq_sound:true
    (LowTactics.gentac_of_any_tac_arg fresh_trace_tac fresh_equiv_tac)
