open Utils
open Rewrite

module Args = TacticsArgs
module L = Location

module T = Prover.ProverTactics

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
    (LT.gentac_of_any_tac_arg TraceTactics.case_tac EquivTactics.case_tac)

(*------------------------------------------------------------------*)
let yes_no_if_tac b (args : TacticsArgs.parser_args) s =
  match s with
  | Goal.Trace s -> LT.wrap_fail (TraceTactics.yes_no_if_args b args) s
  | Goal.Equiv s -> LT.wrap_fail (EquivTactics.yes_no_if_args b args) s

(* TODO: remove tactics (subsumed by `rewrite`) *)
let () =
  T.register_general "noif"
    ~tactic_help:{
      general_help = "Simplify conditional by showing that its condition is False.";
      detailed_help = "";
      tactic_group = Structural;
      usages_sorts = [Sort None] }
   (yes_no_if_tac false)

let () =
  T.register_general "yesif"
    ~tactic_help:{
      general_help = "Simplify conditional by showing that its condition is True.";
      detailed_help = "";
      tactic_group = Structural;
      usages_sorts = [Sort None] }
   (yes_no_if_tac true)


(*------------------------------------------------------------------*)
let () =
  T.register "assumption"
    ~tactic_help:{general_help = "look for the goal in the hypotheses.";
                  detailed_help = "";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    (LT.genfun_of_any_fun TraceTactics.assumption EquivTactics.assumption)

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
      usages_sorts = [Sort None; Sort Int];
      tactic_group = Structural}
    (LT.gentac_of_any_tac_arg TraceTactics.fa_tac EquivTactics.fa_tac)

(*------------------------------------------------------------------*)
let () =
  T.register_general "fresh"
    ~tactic_help:{
      general_help = "Exploit the freshness of a name.";
      detailed_help = "Local sequent:\n\
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
    (LT.gentac_of_any_tac_arg TraceTactics.fresh_tac EquivTactics.fresh_tac)

(*------------------------------------------------------------------*)
let () = T.register_general "induction"
    ~tactic_help:{
      general_help = "Apply the induction scheme to the conclusion.";
      detailed_help = "";
      usages_sorts = [Sort None];
      tactic_group = Logical}
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

let tac_auto ~strong ~close args s sk fk = match s with
  | Goal.Trace s ->
    let sk l fk =
      sk (List.map (fun s -> Goal.Trace s) l) fk
    in
    TraceTactics.tac_auto ~close ~strong args s sk fk
  | Goal.Equiv _ -> EquivTactics.tac_auto ~close ~strong args s sk fk

let () =
  T.register_general "autosimpl"
    ~tactic_help:{general_help = "Simplify a goal, without closing \
                                  it. Automatically called after each tactic.";
                  detailed_help = "";
                  usages_sorts = [Sort None];
                  tactic_group = Structural}
    tac_autosimpl
    
let () = 
  T.register_general "simpl"
    ~tactic_help:{general_help = "Simplifies a goal, without closing it.";
                  detailed_help = "";
                  usages_sorts = [Sort None];
                  tactic_group = Structural}
    (tac_auto ~close:false ~strong:true)
    
let () =
  T.register_general "auto"
    ~tactic_help:{general_help = "Closes a goal.";
                  detailed_help = "Stronger automation than simpl.";
                  usages_sorts = [Sort None];
                  tactic_group = Structural}
    (tac_auto ~close:true ~strong:true)

(*------------------------------------------------------------------*)
let () =
  T.register_general "rewrite"
    ~tactic_help:{
      general_help =
        "If t1 = t2, rewrite all occurences of t1 into t2 in the goal.\n\
         Usage: rewrite Hyp Lemma Axiom (forall (x:message), t = t').\n       \
         rewrite Lemma Axiom (t=t').\n       \
         rewrite (forall (x:message), t = t').\n       \
         rewrite (t = t') Lemma in H.";
      detailed_help = "";
      usages_sorts  = [];
      tactic_group  = Structural;}
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
    (LT.intro_tac (tac_auto []))
