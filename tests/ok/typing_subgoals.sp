(* This file tests the tactics `typing`.
   This file checks the creation of subgoals by the tactic.
   First, it declares a system using different constants.
   Then it uses tests the tactics to generates three subgoals:
   - one for different constant
   - one created by an output macro
   - one created by an state macro
   Finally, it uses the tactic to checke the filtering of hypothesis. *)

set securityTypes = true.

channel c
name n : message
mutable s : message, Low = empty
abstract a : message
abstract b : message
abstract d : message.
axiom[any] ax1 : a <> b.
axiom[any] ax2 : a <> d.

system sys1 = (in(c, x); out(c,if diff(a<>b, d<>a) then empty else n)).
Proof.
  apply ax1.
Qed.
Proof.
  apply ax2.
Qed.

name h : message, High
name l : message, Low.

lemma[sys1] _ : h=l => false.
Proof.
  intro H.
  typing H.
Qed.

system sys = null.

lemma[sys/right] _ : h = if a<>b then <output@init, s@init> => false.
Proof.
  intro H.
  typing H.
  - apply ax1.
  - intro _.
    rewrite /exec.
    true.
  - intro _.
    constraints.
Qed.
global lemma[sys] _ : Forall (tau1 : timestamp) (tau2 : timestamp[const]) (x : message),
  [tau1 <> init] -> [tau2 <> init => exec@tau2 => exec@tau1 => h=output@init => false].
Proof.
  intro tau1 tau2 x H1.
  intro H2 H3 H4 H.
  typing H.
  (*The tactic must keep the hypothesis that is global [H1] or const [H2] or type Bool [H3].
    Other hypothesis are removed*)
  - clear H1.
    clear H2.
    clear H3.
    checkfail clear H4 exn Failure.
    auto.
  - auto.
Qed.
