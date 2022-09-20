(** Tactics exploiting a name's freshness. *)

open Term

module NO = NameOccs

module TS = TraceSequent
module ES = EquivSequent

module Hyps = TS.LocalHyps

module MP = Match.Pos
module Sp = Match.Pos.Sp

open LowTactics

(*------------------------------------------------------------------*)
let wrap_fail_trace = TraceLT.wrap_fail
let wrap_fail_equiv = EquivLT.wrap_fail

let soft_failure = Tactics.soft_failure
(* let hard_failure = Tactics.hard_failure *)

type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
(* Look for occurrences using NameOccs *)

(** A (unit,unit) NO.f_fold_occs function, for use with NO.occurrence_goals.
    Looks for occurrences of n in t (ground):
    - if t is n: returns the occurrence
    - otherwise: asks to be called recursively on subterms.
   uses not accumulator, so returns an empty unit list. *)
let get_bad_occs
    (n:nsymb) 
    (retry_on_subterms : unit -> NO.n_occs * NO.empty_occs)
    (rec_call_on_subterms : 
       (fv:Vars.vars ->
        cond:terms ->
        p:MP.pos ->
        info:NO.expand_info ->
        st:term -> 
        term ->
        NO.n_occs * NO.empty_occs))
    ~(info:NO.expand_info)
    ~(fv:Vars.vars)
    ~(cond:terms)
    ~(p:MP.pos)
    ~(st:term)
    (t:term) : NO.n_occs * NO.empty_occs
  =
  (* handles a few cases, using rec_call_on_subterm for rec calls,
     and calls retry_on_subterm for the rest *)
  match t with
  | Var v when not (Type.is_finite (Vars.ty v)) ->
    soft_failure
      (Tactics.Failure "can only be applied on ground terms")

  | Name nn when nn.s_symb = n.s_symb ->
    [NO.mk_nocc nn n fv cond (fst info) st], []

  | _ -> retry_on_subterms ()




(*------------------------------------------------------------------*)
(** Fresh trace tactic *)

(** Computes parameters for the fresh trace tactic:
    returns n, t such that hyp is n = t or t = n
    (looks under macros if possible *)
let fresh_trace_param
    ~(hyp_loc : L.t) 
    (info : NO.expand_info) 
    (hyp : term)
    (s : TS.sequent)
  : nsymb * term
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
    | Name ns, _ -> (ns, em2)
    | _, Name ns -> (ns, em1)
    | _ ->
      soft_failure ~loc:hyp_loc
        (Tactics.Failure "can only be applied on an hypothesis of \
                          the form t=n or n=t")
  in
  let ty = n.s_typ in
  if not Symbols.(check_bty_info table ty Ty_large) then
    Tactics.soft_failure
      (Failure "the type of this term is not [large]");

  (n, t)


(** Applies fresh to the trace sequent s and hypothesis m:
    returns the list of subgoals with the added hyp that there is a collision *)
let fresh_trace (m : lsymb) (s : TS.sequent) : TS.sequent list =
  let id, hyp = Hyps.by_name m s in
  try
    let contx = TS.mk_trace_cntxt s in
    let env = (TS.env s).vars in
    let (n, t) =
      fresh_trace_param ~hyp_loc:(L.loc m) (NO.EI_direct, contx) hyp s
    in

    let pp_n ppf () = Fmt.pf ppf "%a" Term.pp_nsymb n in
    let get_bad = get_bad_occs n in
   
    Printer.pr "Freshness of %a:@; @[<v 0>" pp_n ();
    let phis  =
      NO.name_occurrence_formulas ~pp_ns:(Some pp_n)
        get_bad contx env [t]
    in
    Printer.pr "@]@;";

    let g = TS.goal s in
    List.map
      (fun phi ->
         TS.set_goal (mk_impl ~simpl:false phi g) s)
      phis
  with
  | SE.(Error Expected_fset) ->
    soft_failure Underspecified_system



(** fresh trace tactic *)
let fresh_trace_tac args s =
  match TraceLT.convert_args s args (Args.Sort Args.String) with
  | Args.Arg (Args.String str) -> wrap_fail_trace (fresh_trace str) s
  | _ -> bad_args ()





(*------------------------------------------------------------------*)
(** Fresh equiv tactic *)
(* Constructs the formula expressing the freshness
   of the proj of t in the proj of the biframe,
   provided it is a name member of a large type *)
let phi_proj
    (loc:L.t)
    (contx:Constr.trace_cntxt)
    (env:Vars.env)
    (t:term)
    (biframe:terms)
    (proj:proj) :
  terms
  =
  let table = contx.table in
  let system_p = SE.project [proj] contx.system in
  let contx_p = { contx with system = system_p } in
  let info_p = (NO.EI_direct, contx_p) in
  let t_p = NO.expand_macro_check_all info_p (Term.project1 proj t) in
  let n_p  = match t_p with
    | Name np -> np
    | _ -> soft_failure ~loc
             (Tactics.Failure "Can only be applied to diff(n_L, n_R)")
  in
  let ty_p = n_p.s_typ in
  if not Symbols.(check_bty_info table ty_p Ty_large) then
    Tactics.soft_failure ~loc
      (Tactics.Failure "the type of this term is not [large]");
  let frame_p = List.map (Term.project1 proj) biframe in
  let pp_n_p ppf () = Fmt.pf ppf "%a" Term.pp_nsymb n_p in
  let get_bad_p = get_bad_occs n_p in
  
  (* the biframe is used in the old fresh for indirect cases. why? *)
  (* should env be projected? *)
  let phi_p =
    NO.name_occurrence_formulas
      ~negate:true ~pp_ns:(Some pp_n_p)
      get_bad_p contx_p env frame_p
  in

  (* not removing duplicates here, as we already do that on occurrences. *)
  (* probably fine, but we'll need to remove duplicates between phi_l and phi_r *)
  phi_p



(* Constructs the sequent where goal i, if of the form diff(n_l, n_r),
   is replaced with if phi then zero else diff(n_l, n_r),
   where phi expresses the freshness of n_l on the left, and n_r on the right *)
let fresh_equiv (i : int L.located) (s : ES.sequent) : ES.sequents =
  let contx = ES.mk_pair_trace_cntxt s in
  let env = ES.vars s in
  let loc = L.loc i in

  let proj_l, proj_r = ES.get_system_pair_projs s in

  let before, t, after = split_equiv_goal i s in
  let biframe = List.rev_append before after in
  
  Printer.pr "@[<v 0>Freshness on the left side:@; @[<v 0>";
  let phi_l = phi_proj loc contx env t biframe proj_l in

  Printer.pr "@]@,Freshness on the right side:@; @[<v 0>";
  let phi_r = phi_proj loc contx env t biframe proj_r in
  Printer.pr "@]@]@;";

  (* Removing duplicates. We already did that for occurrences, but
     only within phi_l and phi_r, not across both *)
  let cstate = Reduction.mk_cstate contx.table in
  let phis = Utils.List.remove_duplicate (Reduction.conv cstate) (phi_l @ phi_r) in

  let phi = mk_ands ~simpl:true phis in
  let new_t = mk_ite ~simpl:true phi mk_zero t in
  let new_biframe = List.rev_append before (new_t::after) in
  [ES.set_equiv_goal new_biframe s]



(* fresh equiv tactic *)
let fresh_equiv_tac args = match args with
  | [Args.Int_parsed i] -> wrap_fail_equiv (fresh_equiv i)
  | _ -> bad_args ()
