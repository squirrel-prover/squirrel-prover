open Utils

module Args = TacticsArgs
module L = Location

module T = ProverTactics

module LT = LowTactics

module St = Term.St
module Sv = Vars.Sv

type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
let dbg = LT.dbg

(*------------------------------------------------------------------*)
let hard_failure = Tactics.hard_failure
let soft_failure = Tactics.soft_failure

(*------------------------------------------------------------------*)
let bad_args = LT.bad_args

(*------------------------------------------------------------------*)
let () =
  T.register_general "case"
    ~tactic_help:
      {general_help = "Perform a case analysis.";
       detailed_help = "";
       usages_sorts = [Sort Args.Timestamp;
                       Sort Args.String;
                       Sort Args.Message;];
       tactic_group = Logical}
    ~pq_sound:true
    (LT.gentac_of_any_tac_arg TraceTactics.case_tac EquivTactics.case_tac)


(*------------------------------------------------------------------*)
let () =
  T.register_general "assumption"
    ~tactic_help:{general_help = "Concludes if the goal or false appears \
                                  in the hypotheses.";
                  detailed_help = "";
                  usages_sorts = [Sort None; Sort String];
                  tactic_group = Logical}
    ~pq_sound:true
    (LT.gentac_of_any_tac_arg
       TraceTactics.assumption_tac
       EquivTactics.assumption_tac)

(*------------------------------------------------------------------*)
let () =
  T.register_general "constraints"
    ~tactic_help:{
      general_help =  "Tries to derive false from the trace formulas.";
      detailed_help = "From ordering constraints on the timestamps, \
                       checks that we can build an acyclic graph on \
                       them, i.e., if they are a possible trace.";
      usages_sorts = [Sort None];
      tactic_group = Structural}
    ~pq_sound:true
    (LT.gentac_of_any_tac_arg
       TraceTactics.constraints_tac
       EquivTactics.constraints_tac)

(*------------------------------------------------------------------*)
let () =
  T.register_general "fa"
    ~tactic_help:{
      general_help = "Apply the function application rule.";
      detailed_help = "Local sequent:\n\
                       When we have G => f(u) = f(v), produces the \
                       goal G => u=v. Produces as many subgoals as \
                       arugment of the head function symbol.\n\
                       Global sequent:\n\
                       To prove that a goal containing f(u1,...,un) is \
                       diff-equivalent, one can prove that the goal containing the \
                       sequence u1,...,un is diff-equivalent.";
      usages_sorts = [Sort None; Sort Int; Sort Term];
      tactic_group = Structural}
    ~pq_sound:true
    (LT.gentac_of_any_tac_arg TraceTactics.fa_tac EquivTactics.fa_tac)


(*------------------------------------------------------------------*)
let () = T.register_general "induction"
    ~tactic_help:{
      general_help = "Apply the induction scheme to the conclusion.";
      detailed_help = "Only support induction over finite types.";
      usages_sorts = [Sort None];
      tactic_group = Logical}
    ~pq_sound:true
    (LT.gentac_of_any_tac_arg
       (LT.TraceLT.induction_tac ~dependent:false)
       EquivTactics.old_or_new_induction)

(*------------------------------------------------------------------*)
(* Remark: EquivTactics and TraceTactics implementation of [tac_autosimpl]
   slightly differ, because the [strong] flag is always [true]
   in [TraceTactics.tac_autosimpl] when [Config.auto_intro ()] is [true].
   Because of this, there is some code replication below, to reflect this
   asymmetry. *)

let tac_autosimpl args s sk fk = match s with
  | Goal.Trace s ->
    let sk l fk =
      sk (List.map (fun s -> Goal.Trace s) l) fk
    in
    TraceTactics.tac_autosimpl args s sk fk
  | Goal.Equiv _ -> EquivTactics.tac_autosimpl args s sk fk

let tac_auto : 'a list -> LowTactics.f_simpl =
  fun args ~red_param ~strong ~close s sk fk -> 
  match s with
  | Goal.Trace s ->
    let sk l fk =
      sk (List.map (fun s -> Goal.Trace s) l) fk
    in
    TraceTactics.tac_auto ~red_param ~close ~strong args s sk fk
  | Goal.Equiv _ -> EquivTactics.tac_auto ~red_param ~close ~strong args s sk fk

let () =
  T.register_general "autosimpl"
    ~tactic_help:{general_help = "Simplify a goal, without closing \
                                  it. Automatically called after each tactic.";
                  detailed_help = "";
                  usages_sorts = [Sort None];
                  tactic_group = Structural}
    ~pq_sound:true
    tac_autosimpl

let () =
  (* FEATURE: allow user to change [red_param] *)
  let red_param = Reduction.rp_default in
  T.register_general "simpl"
    ~tactic_help:{general_help = "Simplifies a goal, without closing it.";
                  detailed_help = "";
                  usages_sorts = [Sort None];
                  tactic_group = Structural}
    ~pq_sound:true
    (tac_auto ~red_param ~close:false ~strong:true)

let () =
  (* FEATURE: allow user to change [red_param] *)
  let red_param = Reduction.rp_default in
  T.register_general "auto"
    ~tactic_help:{general_help = "Closes a goal.";
                  detailed_help = "Stronger automation than simpl.";
                  usages_sorts = [Sort None];
                  tactic_group = Structural}
    ~pq_sound:true
    (tac_auto ~red_param ~close:true ~strong:true)

(*------------------------------------------------------------------*)
let () =
  T.register_general "rewrite"
    ~tactic_help:{
      general_help =
        "If t1 = t2, rewrite all occurences of t1 into t2 in the goal.\n\
         Usage: rewrite Hyp Lemma Axiom.\n       \
         rewrite Lemma Axiom.\n       \
         rewrite Lemma in H.";
      detailed_help = "";
      usages_sorts  = [];
      tactic_group  = Structural;}
    ~pq_sound:true
    (LT.rewrite_tac (tac_auto []))

(*------------------------------------------------------------------*)
let () =
  T.register_general "intro"
    ~tactic_help:{
      general_help = "Introduce topmost connectives of conclusion \
                      formula, when it can be done in an invertible, \
                      non-branching fashion.\
                      \n\nUsage: intro a b _ c *";
      detailed_help = "";
      usages_sorts = [];
      tactic_group = Logical}
    ~pq_sound:true
    (LT.intro_tac (tac_auto []))
