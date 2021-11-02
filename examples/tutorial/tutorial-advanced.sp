(*

We present in this tutorial some more advanced features of the tactic language such as:
 - basic intro patterns
 - shortcuts for intros and rewrite (ss reflect style)
 - complex rewrites

Be aware that such constructs may ease proof writing sometime at the cost of readability for less experienced users.
*)



channel c
abstract ok:message
abstract f : boolean
abstract g : boolean
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
Proof. intro *.   (* select names automaticaly *)
Abort.

goal _ : f => false.
Proof. intro H.   (* use given name *)
Abort.

goal _ : forall x:message, h(x) => false.
Proof. intro y H.   (* use given name also for variables *)
Abort.


goal _ : f => g => (forall x:message, h(x) => false).
Proof. intro Hf Hg y *.   (* the introduction is chained *)
Abort.
(* Patterns also allow to directly split more complex formulas. *)


goal _ : f && g =>false.
Proof. intro Hconj.   (* Here, without further infos, we obtain two hypothesis named by default *)
Abort.

goal _ : f && g =>false.
Proof. intro [Hf Hg].   (* the pattern [f1 fs] allows to name hypothesis for f1 && ... && fs *)
Abort.


goal _ : f || g =>false.
Proof. intro [Hf | Hg].   (* the pattern [f1 | ... | fs] allows to name hypothesis for all the subgoals created by splitting f1 || ... || fs *)
Abort.

goal _ : (f || g) && f =>false.
Proof. intro [[Hf | Hg] Hf2].   (* patterns can be combined in any ways *)
Abort.

goal _ : (f || g) && f =>false.
Proof. intro [[Hf | Hg] _].   (* names can be droped if useless, with _ *)
Abort.


(*
By default, automatic introduction are performed after every tactic.
*)
goal _ (x,y:message): if true then x else y=x.
Proof.
yesif.
Qed.


(* While this allows to efficiently close many trivial goals, advanced users may prefer to control this behabiour themselves. It can be disabled with the following command. *)
set autoIntro=false.
goal _ (x,y:message): if true then x else y=x.
Proof.
yesif; auto.
Qed.

(*

# Shortcuts in SS reflect style

Some syntactic sugar allow to quickly combine intros, rewrites and macro expansions.

## Intro after a tactic

For instance, `tactic; intros PAT`, where the intro pattern is performed on every subgoal can be written with `tactic => PAT`.
*)

set autoIntro=false.
goal _ (x,y:message): (x=y => false) || (x<> y => false) .
Proof.
case x=y => XY.  (* the hypothesis introduced by the case is introduced in both subgoals as XY *)
by right.
by left.
Qed.


(* Tactics can be applied only to a subgroup of the subgoals, using their number to identify them. *)

goal _ (x,y:message): (x=y => false) || (x<> y => false) .
Proof.
case x=y => XY; 1: by right.  (* Apply by right to the first subgoal created *)

by left.
Qed.


(*

Additionally, special symbols in pattern allow to perform automatic simplifications.
 - `//` applies `try auto` in all subgoals (leaving the one not closed without any simplifcations)
 - `/=` applies `simpl` in all subgoals, simplifying all as much as possible without closing any.
*)

goal _ (x,y,z:message): true => true .
Proof.
intro _ => //.
Qed.

(*

Those symbols can also be followed by intro patterns.

*)

abstract m : message->message.

goal _ (x,y:message): m(x) = x => if true then x else y= m(x).
Proof.
yesif => // => /= t.
Qed.

(*

## Rewrites inside patterns

Sometimes, instead of introducing an equation, we want to apply it instantly to the conclusion and then forget about it. *)

(* Typically, in the following example, we would want to forget about Hxy. *)
goal _ (x,y:message): h(x)=h(y) => h(x) = g.
Proof.
intro Hxy.
rewrite Hxy.
Abort.

(* This is achieved by using -> instead of a name for an hypothesis. *)
goal _ (x,y:message): h(x)=h(y) => h(x) = g.
Proof.
intro ->.
Abort.

(*
## Macro expansion inside patterns

 During an intro pattern, it can be useful to expand a macro before continuing the introduction. E.g., in the following example, expanding cond in the middle of intro would allow to also introduce what is inside the condition.  *)
abstract ko:message.
goal unforgeable:
  happens(A) =>  cond@A => ko <> ok => output@A <> ko.
Proof.
  nosimpl(intro Hap Hcond Hdiff).
  nosimpl(expand cond).
  nosimpl(destruct Hcond as [Hf Hg]).
Abort.

(* All those operations can be expressed in a single one by inserting inside the intro pattern @/sym, that will expand sym in the current state of the intro, and then carry on with the introduction. *)
goal unforgeable:
  happens(A) =>  cond@A => ko <> ok => output@A <> ko.
Proof.
  nosimpl(intro Hap @/cond [Hf Hg] Hdiff).
Abort.



(*```


# Rewrite

By default, and as seen before, rewrites are performed over the conclusion by giving the name of an hypothesis.
`rewrite H1 ... Hn` will rewrite according to the equations given by `H1` to `Hn` the first occurence matching in the conclusion.
By default, equations are interpreted from left to right. But the direction can be reversed with `-H`.
`rewrite H in C1,...,C2` allows to rewrite in hypothesis instead of conclusion.

```*)

goal _ (x,y:message): h(x)=h(y) => h(x) = g => false.
Proof.
intro eq.
rewrite eq.
(* and we now we go on the other direction, going back to the initial state. *)
rewrite -eq.

intro C.
rewrite eq in C.
Abort.

(*

Rewrites can also be performed in the equivalence context by giving the frame element identifers.

Rewrites will fail if there is nothing to rewrite. `rewrite !H` allows to rewrite all occurences found. `rewrite ?H` is the same but does not fail if there is nothing to rewrite.

Rewrites can be used to expand in place macros, with for instance `rewrite /cond`.

If the hypothesis is an implication, the rewrite will rewrite in the current goal and add the subgoal for the premice.

Finally, rewrites can be over a quantified formula that we may partially instantiate with some variables.


*)

abstract P : message -> message -> boolean.
abstract k : message -> message.
abstract a : message.
abstract b : message.
goal _ (z : message) :
  (forall (x,y : message), P(x,y) => k(y) = x) =>
   P(a, z) => <k(z),b> = <a, b>.
Proof.
  intro H Assum.
  rewrite (H a).
  (* Here, (H a) produces the equation foral y, P(a,y) => k(y)=a *)
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
