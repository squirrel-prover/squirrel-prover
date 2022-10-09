(*

We present in this tutorial some more advanced features of the tactic language such as:
 - basic intro patterns
 - shortcuts for intros and rewrite (ss reflect style)
 - complex rewrites

Be aware that such constructs may ease proof writing sometime at the cost of readability for less experienced users.
*)



channel c
abstract ok : message
abstract f  : boolean
abstract g  : boolean
system if f && g then out(c,ok).


(*

# Intro patterns

Squirrel's tactic language supports some of the intro patterns from
(Coq)[https://coq.inria.fr/refman/proof-engine/tactics.html#intro-patterns]

Such patterns allow to specify how new hypothesis should be introduced, e.g. by an intro or a destruct.

In the most basic setting, an intro patten simply provide names, either for variables or the hypothesis identifiers.

```*)

abstract h : message -> boolean.


goal _ : f => false.
Proof. intro *.   (* names can be given automaticaly *)
Abort.

goal _ : f => false.
Proof. intro H.   (* hypotheses can be named manually *)
Abort.

goal _ : forall x:message, h(x) => false.
Proof. intro y. (* variables can be named manually *)
Abort.


goal _ : f => g => (forall x:message, h(x) => false).
Proof. intro Hf Hg y *.   (* the introductions are chained *)
Abort.
(* Patterns also allow to directly split more complex formulas. *)


goal _ : (f && g) => false.
Proof. intro Hconj.  (* Here, without further infos, we obtain two hypothesis named by default *)
Abort.

goal _ : (f && g) =>false.
Proof. intro [Hf Hg].   (* the pattern [f1 ... fs] allows to name hypotheses for a formula f1 && ... && fs *)
Abort.


goal _ : (f || g) =>false.
Proof. intro [Hf | Hg].   (* the pattern [f1 | ... | fs] allows to name hypotheses for all the subgoals created by splitting f1 || ... || fs *)
Abort.

goal _ : ((f || g) && f) =>false.
Proof. intro [[Hf | Hg] Hf2].   (* patterns can be nested *)
Abort.

goal _ : ((f || g) && f) => false.
Proof. intro [[Hf | Hg] _].   (* names can be dropped if useless, with _ *)
Abort.


(** Include basic standard library, important helper lemmas and
    setting proof mode to autoIntro=false. *)
include Basic.

(* The library notably contains an equation allowing to simplify a trivial if. *)
goal _ (x,y:message): if true then x else y=x.
Proof.
rewrite if_true.
auto.
auto.
Qed.

(*

# Shortcuts in SS reflect style

Some syntactic sugar allow to quickly combine intros, rewrites and macro expansions.

## Intro after a tactic

For instance, `tactic; intros PAT`, applies the intro pattern `PAT` to every subgoal created by `tactic`. This can be written more concisely using `tactic => PAT`.
*)

goal _ (x,y:message): (x=y => false) || (x<> y => false) .
Proof.
case x=y => XY.  (* the hypothesis introduced by the case is introduced in both subgoals as XY *)
by right.
by left.
Qed.


(* Tactics can be applied only to a subset of the new subgoals, by selecting subgoals using their number. *)

goal _ (x,y:message): (x=y => false) || (x<> y => false) .
Proof.
case x=y => XY; 1: by right.  (* Apply by right to the first subgoal created *)

by left.
Qed.


(*
Additionally, special symbols in pattern allow to perform automatic simplifications.
 - `//` applies `try auto` in all subgoals (leaving the one not closed without any simplifcations)
 - `/=` applies `simpl` in all subgoals, simplifying all as much as possible without closing any.
 - `//=` combines `//` and `/=`.
*)

goal _ (x,y,z:message): true => true .
Proof.
intro _ => //.
Qed.

(*
These simplification patterns can be chained and combined with introduction patterns.
*)

abstract m : message->message.

goal _ (x,y:message): m(x) = x => if true then x else y= m(x).
Proof.
rewrite if_true => //= t.
Qed.

(*

## Rewrites inside patterns

Sometimes, instead of introducing an equation, we want to apply it instantly to the conclusion and then clear it (i.e. forget it). *)

(* Typically, in the following example, we do not need Hxy after the rewriting. *)
goal _ (x,y:message): h(x)=h(y) => h(x) = g.
Proof.
intro Hxy.
rewrite Hxy.
clear Hxy.
Abort.

(* This is achieved more concisely using ->. *)
goal _ (x,y:message): h(x)=h(y) => h(x) = g.
Proof.
intro ->.
Abort.

(*
## Macro expansion inside patterns

 During an intro pattern, it can be useful to expand a macro before continuing the introduction. E.g., in the following example, expanding cond in the middle of intro allow to detruct directly the condition.  *)
abstract ko:message.

goal unforgeable:
  happens(A) =>  cond@A => ko <> ok => output@A <> ko.
Proof.
  intro Hap Hcond Hdiff.
  expand cond.
  destruct Hcond as [Hf Hg].
Abort.

(* All those operations can be done using a single intro pattern, using the intro pattern @/sym, which expands the sym macro in the goal. Note that sym is only expanded in the goal, not the hypotheses. *)
goal unforgeable:
  happens(A) =>  cond@A => ko <> ok => output@A <> ko.
Proof.
  intro Hap @/cond [Hf Hg] Hdiff.
Abort.



(*```


# Rewrite

By default, and as seen before, rewrites are done in the goal, selecting rewrite rules using the hypotheses' names.
`rewrite H1 ... Hn` rewrites the goal according to the equations given by `H1` to `Hn`. Each time, we rewrite all occurrences of the first the occurence matching `Hi` the conclusion.
By default, rewriting are from left to right. The direction can be reversed with `-H`.
By default, rewrite acts on the goal. The syntax `rewrite H in C1,...,C2` allows to rewrite in the hypotheses instead of conclusion. To rewrite in the whole judgement (hypotheses + goal), we can use `rewrite H in *`.

```*)

abstract test : message -> message.

goal _ (x,y:message): h(x) = h(y) => h(x) = h(x) => false.
Proof.
intro eq.
rewrite eq.
(* and we now we go on the other direction, going back to the initial state. *)
rewrite -eq.


Abort.

(*

Rewrite rule can have universally quantified variables, which must be automatically inferred (by matching).

Rewrites can also be performed in the equivalence context by giving the frame element identifers.

A rewrite will fail if there is nothing to rewrite. `rewrite !H` rewrites `H` as much as possible, but at least once. `rewrite ?H` is identical to `rewrite !H`, but does not fail if there is nothing to rewrite.

Rewrites can be used to expand macros, using the syntax `rewrite /cond`.

If the hypothesis `H` is a rewrite rule with premises, `rewrite H` will add the premises (instantiated using the arguments infered during the matching) as subgoals.

Finally, universally quantified variables in rewrite rules can be partially instantiated.

*)

abstract P : message * message -> boolean.
abstract k : message -> message.
abstract a : message.
abstract b : message.
goal _ (z : message) :
  (forall (x,y : message), P(x,y) => k(y) = x) =>
   P(a, z) => <k(z),b> = <a, b>.
Proof.
  intro H Assum.
  rewrite (H a).
  (* Here, (H a) produces the equation forall y, P(a,y) => k(y)=a *)
  assumption.
  congruence.
Qed.

(* If the variable we want to instantiate is not the first one, we can use _ to leave some variables free. *)

goal _ (z : message) :
  (forall (x,y : message), P(y,x) => k(x) = y) =>
   P(a, z) => <k(z),b> = <a, b>.
Proof.
  intro H Assum.
  (* here we swapped x and y in the formula, so we now need to instantiate y with a*)
  rewrite (H _ a).
  assumption.
  congruence.
Qed.


(*

## Automatic solver

Rewrite tactics can be added to the automatic constraint solving procedure by using the `hint` keyword outside of the context of a proof, followed by the rewrite rule.
Always make sure that the resulting Term Rewriting System is terminating.

 *)

axiom split_k (x,y : message) :  k (<x,y>) = x.

hint rewrite split_k.

goal _ (a,b,c : message) : a = c => k(<a,b>) = c.
Proof.
 intro H.
 (* simpl will now automatically apply the rewrite rule of split_k *)
 simpl.
 assumption.
Qed.
