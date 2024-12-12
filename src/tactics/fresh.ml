(** Tactics exploiting a name's freshness. *)
open Squirrelcore
open Utils
open Ppenv

module TS = TraceSequent
module ES = EquivSequent

module MP = Match.Pos
module Sp = Match.Pos.Sp

open LowTactics

(*------------------------------------------------------------------*)
let soft_failure = Tactics.soft_failure
let hard_failure = Tactics.hard_failure

type lsymb = Typing.lsymb

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

module O = Occurrences
module Name = O.Name 
module NOC = O.NameOC
module NOS = O.NameOS
module NOF = O.NameOF


(** Look for occurrences using [Occurrences].
    A [NOS.f_fold_occs] function.
    Looks for occurrences of [n] in [t]:
    - if [t] is an name with the same symbol as [n]: returns the occurrence,
      and look recursively in the arguments
    - otherwise: asks to be called recursively on subterms.
      Do not uses an accumulator, so returns an empty unit list. *)
let get_bad_occs
    (n : Name.t) 
    ~(retry : unit -> NOS.simple_occs)
    ~(rec_call : O.pos_info -> Term.term -> NOS.simple_occs) 
    (info : O.pos_info)
    (t : Term.term) 
  : NOS.simple_occs
  =
  (* handles a few cases, using [rec_call] for rec calls,
     and calls [retry] for the rest *)
  match t with
  (* a name with the symbol we want: build an occurrence,
     and also look in its args *)
  | Name (nn, nn_args) when nn.s_symb = n.symb.s_symb ->
    (* keep the same info: all good except the Match.pos is not kept
       up to date.
       still fine, since we don't actually use it. *)
    (* in fact here we could just rec_call_on_subterms. *)
    let occs = List.concat_map (rec_call info) nn_args in
    (NOS.EO.SO.mk_simple_occ
       ~content:(Name.of_term t) ~collision:n ~data:()
       ~vars:info.pi_vars
       ~cond:info.pi_cond
       ~typ:info.pi_occtype
       ~sub:info.pi_subterm
       ~show:Show) :: occs

  | _ -> retry ()



(** For a name [n] and terms [tt],
    computes a list of formulas whose disjunction expresses that
    [n] occurs in [tt] or [n.args].
    If [negate] is set to [true], returns the negation, ie a list whose
    conjunction expresses the freshness of [n] in [tt] and [n.args].
    If [checklarge] is set to [true] : ensures that [n]'s type is [large].
    [hyps] are understood in environment [env], and
    [n], [tt] in [env.system.set], which must be the system in [contx]. *)
let phi_fresh_same_system
    ~(negate : bool)
    ~(use_path_cond : bool)
    ~(checklarge : bool)
    ?(loc : L.t option)
    (hyps : Hyps.TraceHyps.hyps) 
    (contx : Constr.trace_cntxt)
    (env : Env.t)
    (n : Term.term)
    (tt : Term.terms)
  : Term.terms =
  (* sanity check: contx and env should agree *)
  assert (SE.equal0 env.system.set ((contx.system) :> SE.arbitrary));
  
  let err = Format.asprintf "%a" Term.pp n in

  let n : Name.t = 
    match n with
    | Name _ -> Name.of_term n
    | _ -> soft_failure ?loc
             (Tactics.Failure ("Term " ^ err ^ " is not a name."))
  in

  (* ensure that the type of the name is large *)
  let ty = n.Name.symb.s_typ in
  if checklarge 
  && not Symbols.TyInfo.(check_bty_info env.table ty Large) then
    Tactics.soft_failure ?loc
      (Tactics.Failure ("the type of term "^err^" is not [large]"));

  let ppe = default_ppe ~table:env.table () in
  let pp_n ppf () = Fmt.pf ppf "occurrences of %a" (Name.pp ppe) n in

  let get_bad : NOS.f_fold_occs = get_bad_occs n in

  let occs =
    NOS.find_all_occurrences ~mode:Iter.NoHonestRand ~pp_descr:(Some pp_n)
      get_bad
      hyps contx env (tt @ n.args)
  in

  List.map (NOF.occurrence_formula ~negate ~use_path_cond) occs



(** Like [phi_fresh_same_system], except that the [hyps] are
    originally understood in environment [env], and
    [n], [tt] in [contx.system], which may refer to different systems.
    Used e.g. when the terms come from a projection, or a system other than
    the sequent's [set]. *)
let phi_fresh
    ~(negate : bool)
    ~(use_path_cond : bool)
    ~(checklarge : bool)
    ?(loc : L.t option)
    (hyps : Hyps.TraceHyps.hyps) 
    (contx : Constr.trace_cntxt)
    (env : Env.t)
    (n : Term.term)
    (tt : Term.terms)
  : Term.terms =
  (* the new environment, where the generated formulas are to be understood *)
  let envp_context = {env.system with set=((contx.system) :> SE.arbitrary)} in
  let envp = Env.update ~system:envp_context env in

  (* keep what trace hypotheses we can going from env.system to
     {set:contx.system, pair:env.system.pair} *)
  let hypsp =
    Hyps.change_trace_hyps_context
      ~old_context:env.system
      ~new_context:envp.system
      ~vars:env.vars ~table:env.table
      hyps
  in

  phi_fresh_same_system
    ~negate ~use_path_cond ~checklarge ?loc
    hypsp contx envp n tt


(** For a term [n] and terms [tt],
    computes a list of formulas whose conjunction expresses that
    [n] is fresh in [tt] and [n.args], after projecting on [proj].
    [hyps] are understood in environment [env], and
    [n], [tt] in [env.system.pair], which must be the system in [contx]. *)
let phi_fresh_proj
    ~(use_path_cond : bool)
    ?(loc  : L.t option)
    (hyps  : Hyps.TraceHyps.hyps) 
    (contx : Constr.trace_cntxt)
    (env   : Env.t)
    (n     : Term.term)
    (tt    : Term.terms)
    (proj  : Projection.t)
  : Term.terms 
  =
  let system = ((Utils.oget env.system.pair) :> SE.fset) in

  (* sanity check: contx and env should agree *)
  assert (SE.equal0 system contx.system);

  (* get the projected system and context
     in which terms are now to be understood *)
  let systemp = SE.project [proj] system in
  let contxp = { contx with system = systemp } in
  let infop = (O.EI_direct, contxp) in

  (* project tt on proj *)
  let ttp = List.map (Term.project1 proj) tt in

  (* project n on proj *)
  let np = O.expand_macro_check_all infop (Term.project1 proj n) in

  phi_fresh
    ?loc ~checklarge:false ~negate:true ~use_path_cond
    hyps contxp env np ttp


(*------------------------------------------------------------------*)
(** {2 Trace fresh tactic} *)

(** Computes parameters for the fresh trace tactic:
    returns n, t such that hyp is n = t or t = n
    (looks under macros if possible *)
let fresh_trace_param
    ~(hyp_loc : L.t) 
    (einfo    : O.expand_info) 
    (hyp      : Term.term)
    (s        : TS.sequent)
  : Term.term * Term.term  
  =
  let m1, m2 = match TS.Reduce.destr_eq s Equiv.Local_t hyp with
    | Some (u, v) -> (u,v)
    | None -> 
      soft_failure ~loc:hyp_loc
        (Tactics.Failure "can only be applied on an equality hypothesis")
  in
  let em1 = O.expand_macro_check_all einfo m1 in
  let em2 = O.expand_macro_check_all einfo m2 in
  match em1, em2 with
  | (Name _ as ns), _ -> (ns, em2)
  | _, (Name _ as ns) -> (ns, em1)
  | _ ->
    soft_failure ~loc:hyp_loc
      (Tactics.Failure "can only be applied on an hypothesis of \
                        the form t=n or n=t")


(** Applies fresh to the trace sequent s and hypothesis m:
    returns the list of subgoals with the added hyp that there is a collision *)
let fresh_trace
    (opt_args : Args.named_args) (m : lsymb) (s : TS.sequent) 
  : TS.sequent list 
  =
  let use_path_cond = p_fresh_arg opt_args in
  let loc = L.loc m in

  if (TS.bound s) <> None then
    soft_failure 
      (Tactics.GoalBadShape "fresh does not handle concrete bounds.");
  
  let _, hyp = TS.Hyps.by_name_k m Hyp s in
  let hyp = as_local ~loc hyp in (* FIXME: allow global hyps? *)
  try
    let contx = TS.mk_trace_cntxt s in
    let env = TS.env s in
    let (n, t) =
      fresh_trace_param ~hyp_loc:(L.loc m) (O.EI_direct, contx) hyp s
    in

    Printer.pr "Freshness of %a:@; @[<v 0>" Term.pp n;
    let phis =
      phi_fresh_same_system (* phi_fresh would work as well *) 
        ~negate:false ~use_path_cond ~checklarge:true ~loc
        (TS.get_trace_hyps s)
        contx
        env
        n
        [t]
    in
    Printer.pr "@]@;";

    let g = TS.conclusion s in
    List.map
      (fun phi ->
         TS.set_conclusion (Term.mk_impl ~simpl:false phi g) s)
      phis
  with
  | SE.(Error (_,Expected_fset)) ->
    soft_failure Underspecified_system


(** fresh trace tactic *)
let fresh_trace_tac (args : TacticsArgs.parser_args) : LowTactics.ttac =
  match args with
  | [Args.Fresh (opt_args, Some (Args.FreshHyp hyp))] -> 
    TraceLT.wrap_fail (fresh_trace opt_args hyp)

  | _ -> bad_args ()




(*------------------------------------------------------------------*)
(** {2 Fresh equiv tactic} *)

(** Constructs the sequent where goal [i], when of the form [diff(n_l, n_r)],
    is removed, and an additional proof obligation [phi] is created,
    where [phi] expresses the freshness of [n_l] on the left, and [n_r] on 
    the right *)
let fresh_equiv
    (opt_args : Args.named_args) (i : int L.located) (s : ES.sequent) 
  : ES.sequents 
  =
  let use_path_cond = p_fresh_arg opt_args in
  let loc = L.loc i in

  let env = ES.env s in
  let pair_context = ES.mk_pair_trace_cntxt s in
  let proj_l, proj_r = ES.get_system_pair_projs s in

  if (ES.conclusion_as_equiv s).bound <> None then 
    soft_failure 
      (Tactics.GoalBadShape "fresh does not handle concrete bounds.");

  let before, t, after = split_equiv_conclusion i s in
  let biframe = List.rev_append before after in

  (* compute the freshness conditions *)
  let phi_fresh_p =
    phi_fresh_proj ~use_path_cond ~loc
      (ES.get_trace_hyps s)
      pair_context
      env
      t biframe
  in
  Printer.pr "@[<v 0>Freshness on the left side:@; @[<v 0>";
  let phi_l = phi_fresh_p proj_l in
  Printer.pr "@]@,Freshness on the right side:@; @[<v 0>";
  let phi_r = phi_fresh_p proj_r in
  Printer.pr "@]@]@;";

  (* Removing duplicates. We already did that for occurrences, but
     only within [phi_l] and [phi_r], not across both *)
  let phis =
    List.remove_duplicate (ES.Reduce.conv_term s) (phi_l @ phi_r)
  in

  let phi = Term.mk_ands ~simpl:true phis in
  let new_biframe = List.rev_append before after in

  (* the sequent for the new proof obligation. *)
  (* TODO: here we ask to prove phi_l & phi_r on [left, right].
     It would be more precise to have diff(phi_l, phi_r). *)

  let freshness_sequent =
    ES.set_conclusion_in_context
      {env.system with set=((pair_context.system) :> SE.arbitrary)}
      (Equiv.mk_reach_atom phi)
      s
  in
  [freshness_sequent;
   ES.set_equiv_conclusion {terms=new_biframe; bound=None} s]


(*------------------------------------------------------------------*)
(** {2 Fresh secrecy tactic} *)


(** From a sequent whose goal is of the form [u *> n],
    closes the goal, and replaces it with a proof obligation [phi],
    where [phi] expresses the freshness of [n].
    Must be used only on secrecy goals. *)
let freshR_secrecy
      (opt_args : Args.named_args) (s : ES.sequent) 
    : ES.sequents 
  =
  let use_path_cond = p_fresh_arg opt_args in

  (* get the components of the secrecy predicate, incl. the system *)
  let sgoal = ES.conclusion_as_secrecy s in
  let env = ES.env s in
  let sec_context =
    Constr.make_context ~table:env.table ~system:(ES.secrecy_system sgoal) in

  
  
  (* compute the freshness conditions *)
  Printer.pr "@[<v 0>Freshness conditions:@; @[<v 0>";
  let phis =
    phi_fresh ~negate:true ~use_path_cond ~checklarge:true
      (ES.get_trace_hyps s)
      sec_context
      env
      (ES.secrecy_right sgoal)
      (ES.secrecy_left sgoal)
  in
  Printer.pr "@]@]@;";

  let phi = Term.mk_ands ~simpl:true phis in

  (* the sequent for the new proof obligation. *)
  if Term.equal phi Term.mk_true then []
  else 
    let freshness_sequent =
      ES.set_conclusion_in_context
        {env.system with set=((sec_context.system) :> SE.arbitrary)}
        (Equiv.mk_reach_atom phi)
        s
    in
    [freshness_sequent]



(** From a sequent whose goal is of the form [u,n,v *> w],
    replaces the goal with [u,v *> w] + a proof obligation [phi],
    where [phi] expresses the freshness of [n].
    Must be used only on secrecy goals. *)
let freshL_secrecy
      (opt_args : Args.named_args) (i:int L.located) (s : ES.sequent) 
    : ES.sequents 
  =
  let use_path_cond = p_fresh_arg opt_args in
  let loc = L.loc i in

  (* get the components of the secrecy predicate, incl. the system *)
  let sgoal = ES.conclusion_as_secrecy s in
  let env = ES.env s in
  let sec_context = 
    Constr.make_context ~table:env.table ~system:(ES.secrecy_system sgoal)
  in

  (* get n *)
  let ii = L.unloc i in
  let uu, n, vv =
    try List.splitat ii (ES.secrecy_left sgoal) with
    | List.Out_of_range ->
       soft_failure ~loc
         (Tactics.Failure 
            ("invalid position "^(string_of_int ii)^" on the left of the predicate"));
  in
  (* compute the freshness conditions *)
  Printer.pr "@[<v 0>Freshness conditions:@; @[<v 0>";
  let phis =
    phi_fresh ~negate:true ~use_path_cond ~checklarge:true ~loc
      (ES.get_trace_hyps s)
      sec_context
      env
      n
      (uu @ vv @ [ES.secrecy_right sgoal])
  in
  Printer.pr "@]@]@;";

  let phi = Term.mk_ands ~simpl:true phis in

  (* the remaining secrecy goal *)
  let ty_left, _ = ES.secrecy_ty sgoal in
  let ty_left,_,ty_left' = List.splitat ii ty_left in
  let ty_left = ty_left @ ty_left' in
  let new_goal = ES.secrecy_update_left ty_left (uu @ vv) sgoal in
  let new_sec_sequent =
    ES.set_conclusion (ES.mk_form_from_secrecy_goal new_goal) s
  in

  (* the sequent for the new proof obligation. *)
  if Term.equal phi Term.mk_true then 
    [new_sec_sequent]
  else 
    let freshness_sequent =
      ES.set_conclusion_in_context
        {env.system with set=((sec_context.system) :> SE.arbitrary)}
        (Equiv.mk_reach_atom phi)
        s
    in
    [freshness_sequent; new_sec_sequent]

(*------------------------------------------------------------------*)
(** {2 Fresh global tactic} *)

(** Dispatches the application of fresh on a global sequent to
    fresh_equiv, freshL_secrecy, or freshR_secrecy *)
let fresh_global_tac (args : TacticsArgs.parser_args)
  : LowTactics.etac =
  EquivLT.wrap_fail
    (fun s ->
       match args with
       (* "fresh i" *)
       | [Args.Fresh (opt_args, Some (Args.FreshInt i))] ->
         (* equivalence goal -> fresh_equiv *)
         if ES.conclusion_is_equiv s then
           fresh_equiv opt_args i s
           (* non-deduction goal -> freshL *)
         else if
           ES.conclusion_is_secrecy s &&
           ES.(secrecy_kind (conclusion_as_secrecy s)) = ES.NotDeduce
         then 
           freshL_secrecy opt_args i s
           (* neither -> bad arguments *)
         else
           bad_args ()

      (* "fresh" *)
      | [Args.Fresh (opt_args, None)] ->
        if ES.conclusion_is_secrecy s &&
           ES.(secrecy_kind (conclusion_as_secrecy s)) = ES.NotDeduce
        then
          freshR_secrecy opt_args s
        else
          bad_args ()

      | _ -> bad_args ())


(*------------------------------------------------------------------*)
let () =
  T.register_general "fresh"
    ~pq_sound:true
    (LowTactics.gentac_of_any_tac_arg fresh_trace_tac fresh_global_tac)
