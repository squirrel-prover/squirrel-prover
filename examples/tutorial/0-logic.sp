(*******************************************************************************
# Basic Logical Reasoning

This file introduces, through a series of simple exercices, the core
tactics allowing to do basic logical reasoning in Squirrel.

Because the objective is do a quick overview of the logical tactics
in Squirrel, the goals below are most of the time trivial.

The syntax for tactics is often inspired from the Coq proof assistant.
Consequently, users familiar with Coq should be able to quickly go
through this file.
*******************************************************************************)

(** Basic setup: this can be ignored. *)
include Basic.
system null.

(* ----------------------------------------------------------------- *)
(** ## A first few simple goals *)

(** In this example, we use a boolean as a proposition:
    it says that if boolean b1 is true, then if boolean b2 is true,
    then boolean b1 && b2 (conjunction) is also true. *)
goal basic_0 : forall (b1, b2 : bool), b1 => b2 => (b1 && b2).
Proof.
  (* Universally quantified variables are introduced in the context
     using `intro`. *)
  intro b1 b2.

  (* Hypotheses can also be introduced. *)
  intro H1 H2.

  (* `split` allows to prove a conjunction by proving both conjuncts.  *)
  split.
  (* Hypothesis `H1` can be applied to conclude using `apply`. *)
  apply H1.
  (* Idem for the second conjunct, with `H2`. *)
  apply H2.
Qed.

goal basic_1 : forall (b1, b2 : bool), (b1 && b2) => (b2 && b1).
Proof.
  intro b1 b2.
  (* When introducing a conjunction, we can split it in two hypotheses. *)
  intro [H1 H2].
  admit. (* TODO *)
Qed.

(** Now we use a boolean with two indices, which can be seen as
    a predicate over pairs of indices. It could mean, for example,
    that the second index is larger than the first, or that they are
    distinct. *)
abstract b : index * index -> bool.

goal basic_2 :
  (forall (i,j:index), b(i,j)) =>
  (forall (k:index), b(k,k)).
Proof.
  (* We group the introduction of forall and =>. *)
  intro H k.
  (* Apply can also use a universally quantified hypothesis.
     Below, `apply H` would be enough as Squirrel can guess
     how to instantiate the universal quantifier,
     but we use this syntax to specify it. *)
  apply H k.
Qed.

goal basic_3 :
  forall (i,j:index),
  b(i,i) =>
  (forall (x:index), b(x,x) => b(j,j)) => 
  b(j,j).
Proof.
  intro i j H1 H2.
  (* Use apply twice to conclude. *)
  admit. (* TODO *)
Qed.

(* ----------------------------------------------------------------- *)
(** ## Disjunctions *)

goal disj_0 : forall (b1,b2:bool), (b1 || b2) => (b2 || b1).
Proof.
  intro b1 b2 H.
  (* We use case to perform a case analysis
     on a disjunctive assumption, which yields 
     two sub-goals. *)
  case H.

  (* -- First sub-goal -- *)
  (* The conclusion is a disjunction,
     we prove it by selecting the right disjunct. *)
  right.
  apply H.

  (* -- Second sub-goal -- *)
  left.
  apply H.
Qed.

goal disj_1 : forall (b1,b2,c:bool),
  (b1 && b2) => ((b1=>c) || (b2=>c)) => c.
Proof.
  admit. (* TODO *)
Qed.

(* ----------------------------------------------------------------- *)
(** ## Rewriting *)

(* Variables `x, y` are introduced by default, because they are
   described before the colon `:`. *)
goal rewrite_0 (x, y, z : message) : x = y => y = z => x = z.
Proof.
  intro H1 H2.

  (* An equality hypothesis `H : u = v` can be used to replace
     occurrences of `u` by `v`, using `rewrite H`. *)
  rewrite H1.
  rewrite H2.

  (* To conclude, we can use the `eq_refl` lemma, which is part of the
     standard library.
     You can print the lemma's statement using `print goal`. *)
  print goal eq_refl.
  apply eq_refl.
Qed.

(* We declare an abstract (i.e. unspecified) predicate `P` over booleans. *)
abstract P : message -> bool.

goal rewrite_1 (x, y : message) : x = y => P(x) => P(y).
Proof.
  intro Heq Hp.

  (* `rewrite` only rewrites in the goal. To rewrite in another
     hypothesis, we can use `rewrite _ in _`. *)
  rewrite Heq in Hp.
  apply Hp.
Qed.

goal rewrite_2 (x, y : message) : (P(y) || y = x) => P(x) => P(y).
Proof.
  admit. (* TODO *)
Qed.

(* ----------------------------------------------------------------- *)
(** ## Existential quantifier *)

(* We first declare a few function symbols, with their types. *)
abstract f : message -> message.
abstract g : message -> message.

goal exists_0 (x, z : message) :
  (forall (y : message), P(f(y))) =>
  (exists (y : message), x = f(y)) =>
  P(x).
Proof.
  intro H1.
  (* An existential hypothesis `exists y, phi` can be opened
     to introduce the witness `y` and an hypothesis `H`
     stating that `phi` holds for y: this is done
     using `intro [y H]` (same syntax than for conjunctions).

     `[y H]` is called an introduction pattern. The pattern `[y H]`
     destructs an existential quantification into its sub-components:
     the witness and the formula that is satisfied.*)
  intro [y H2].
  rewrite H2.
  apply H1.
Qed.

(* Introduction patterns can be nested. E.g., the existential
   `exists y, (phi1 && phi2)` can be introduced with `[y [H1 H2]]`
   (combining an pattern for the existential `[y ...]` with a pattern for
   the conjunction `[H1 H2]`), which yields a witness `y` and two
   hypotheses `H1 : phi1` and `H2 : phi2`. *)
goal exists_1 (x, z : message) :
  (exists (y : message), x = y && y = z) =>
  x = z.
Proof.
  admit. (* TODO *)
Qed.

(* To prove an existential, we can use the `exists y` tactic
   (where `y` is the witness). *)
goal exists_2 (x : message) :
  (exists (y, z : message), x = f(y) && y = f(z)) =>
  (exists (u : message), x = f(f(u))).
Proof.
  intro [y z [H1 H2]].

  (* We provide the witness `z` with `exists z`. *)
  exists z.

  rewrite H1.
  rewrite H2.
  apply eq_refl.
Qed.

(* Use this to prove the following simple lemma.
   Note that if we have an hypothesis `H : u = v`, the tactic
   `rewrite -H` rewrites the equality `u = v` in the converse direction:
   it replaces all occurrences of `v` by `u`. *)
goal exists_3 (x, z : message) :
  (exists (y : message), x = f(y)) =>
  (exists (y : message), f(y) = x).
Proof.
  admit. (* TODO *)
Qed.

(* ----------------------------------------------------------------- *)
(** ## Introducing intermediate goals with `have` *)

goal have_1 (x : message) :
  (forall (y : message), y = f(y) || P(f(y))) =>
  P(x) =>
  P(f(x)).
Proof.
  intro H Hp.
  (* The tactic `have H0 : ...` allows to assert a new hypothesis
     (that we call `H0`), which needs to be proved in the first subgoal
     before being used in the second subgoal. *)
  have H0 : x = f(x) || P(f(x)).
  apply H. (* We prove `H0` by directly applying `H`. *)

  admit. (* TODO *)
Qed.

goal have_2 (x, y : message) :
  (forall (z : message), z = x || P(z)) =>
  P(x) =>
  P(y).
Proof.
  admit. (* TODO *)
Qed.

(* ----------------------------------------------------------------- *)
(** ## Names and freshness *)

(* We declare a few names. *)
name n : message.
name m : message.

(* Recall that names represent uniform random samplings of length
   the security parameter.
   Distinct name symbols are independent random samplings.
   Consequently, the probability of two distinct names being equal is
   negligible. This can be proved using the `fresh` tactic. *)
goal fresh_0 : n = m => false.
Proof.
  intro Eq.
  fresh Eq.
Qed.

(* We can have indexed families of names. *)
name n1 : index -> message.
name m1 : index -> message.

(* Two names `n1(i)` and `n1(j)` represent the same random sampling
   if and only if they have the same indices. *)
goal fresh_1 (i, j : index) : n1(i) = n1(j) => i = j.
Proof.
  admit. (* TODO *)
Qed.

(* Names `n1(i)` and `m2(j)` never represent the same random sampling. *)
goal fresh_2 (i : index) : n1(i) = m1(i) => false.
Proof.
  admit. (* TODO *)
Qed.

(* Actually, the `fresh` tactic can go further: if `t` is a term, and if
   the equality `t = n(j)` holds, then the name `n(j)` must appear somewhere
   in `t`.
   For example, taking `t` to be the tuple
     `<n1(i0), <m1(i1), n1(i2)>>`
   we get that `j` is either `i0` or `i2` (but not `i1`, since only
   `m1(i1)` appears in `t`, not `n1(i1)`). *)
goal fresh_3 (i0, i1, i2, j : index) :
  <n1(i0), <m1(i1), n1(i2)>> = n1(j) =>
  (j = i0 || j = i2).
Proof.
  admit. (* TODO *)
Qed.

(* ----------------------------------------------------------------- *)
(** ## Names and freshness in equivalences *)

(* We write global formulas to reason about equivalences.
   Global and local logical connectives have a different meaning
   but many tactics (`intro`, `apply`, `rewrite`...) behave similarly
   for the two. *)

name k : message.

(* The next goal is a compact way of writing [k,n ~ k,m]. *)
global goal eqnames_0 : equiv(k,diff(n,m)).
Proof.
  (* Fresh names can be removed from an equivalence conclusion.
     The `fresh` tactic used in a global goal behaves quite
     differently from the one use in local goals.
     Here `1` indicates where we want to remove fresh names. *)
  fresh 1.
  (* `fresh` produces a sub-goal to establish freshness. 
      In this example, this is trivial. here freshness is trivial. *)
  auto.
  (* Conclude by reflexivity. *)
  refl.
  (* We could also have applied `fresh` again before
     concluding by reflexity on `equiv()` (an equivalence
     over an empty sequence). *)
Qed.

name n' : index -> message.

(* When freshness is not guaranteed, `fresh` produces an more complicated 
   proof-obligation.
   For the `fresh` tactic to apply, we must require that `i` and `j`
   are constant values: otherwise, they could
   themselves depend on the randomness whose freshness we are 
   exploiting! *)
global goal eqnames_1 (i,j:index[const]) :
  [j<>i] ->
  equiv(n'(i),diff(n'(j),m)).
Proof.
  intro H.
  fresh 1.

  apply H.
  refl.
Qed.

(* In this variant, note that the duplicate item in the equivalence
   is automatically simplified away, which allows to conclude as
   before by freshness. *)
global goal eqnames_1b (i,j:index[const]) :
  [j<>i] ->
  equiv(n'(i),diff(n'(j),m),diff(n'(j),m)).
Proof.
  intro H.
  (* The previous tactic can be decomposed into `nosimpl intro H`
     followed by `simpl` (which has the effect of removing the
     duplicate item). *)
  fresh 1.

  apply H.
  refl.
Qed.

(* Which of the next two goals are provable? *)
global goal eqnames_2a : equiv(diff(n,m),diff(k,n),diff(n,m)).
Proof.
  admit. (* TODO *)
Qed.

global goal eqnames_2b : equiv(diff(k,m),diff(m,n),diff(n,k)).
Proof.
  admit. (* TODO *)
Qed.

(* ----------------------------------------------------------------- *)
(** ## More on equivalences *)

abstract cst : message.

(* Note that `f(diff(x,y))` is equivalent to `diff(f(x),f(y))`. *)
global goal fa_0 (x,y:message) :
  [x=y] -> equiv(diff(y,n)) -> equiv(f(diff(x,n))).
Proof.
  intro Heq Hequiv.
  (* We use `fa` (function application) to simplify the conclusion:
     if
       [  u1...uN, u'1...u'K 
        ~ v1...vN, v'1...v'K ]
     then 
       [  u1...uN, f(u'1...u'K) 
        ~ v1...vN, f(v'1...v'K) ].
     We can target where to apply `fa` through a pattern (here, `f(_)`)
     but we could also specify the equivalence item by its number (here, `0`). *)
  fa f(_). 
  (* alternatively, `fa 0` *)

  rewrite Heq.
  apply Hequiv.
Qed.

global axiom f_equiv : Forall (x:message) equiv(diff(f(x), cst)).

abstract cst' : message.

(* The `apply` tactic can identify non-trivial implications from
   one equivalence to another. Intuitively, we can derive
     `equiv(u1..uN)`
   from
     `equiv(v1..vM)` 
   if the same computation, performed on the left and right projections
   of `v1..vM` yields, respectively, the left and right projections of
  `u1..uN`. 
   This generalizes the reasoning behind `fa`. *)
global goal fa_1 (x:message) : 
  equiv(diff(f(cst'),cst), <cst, f(diff(f(cst'),cst))>).
Proof.
  apply f_equiv.
Qed.

(* The next variant is beyond the scope of a direct application of `apply`
   because of the name `n`: you'll have to handle it explicitly first. *)
global goal fa_2 : 
  equiv(diff(f(cst'),cst), <n, f(diff(f(cst'),cst))>).
Proof.
  admit. (* TODO *)
Qed.


(* ----------------------------------------------------------------- *)
(** ## Combining tactics, automatic reasoning  *)

(* Tactics can be composed using `;`:
   `tac1; tac2` applies the tactic `tac1`, and then
   applies `tac2` to all subgoals produced by `tac1`. *)

(* E.g. the following goal can be proved with a single tactic. *)
goal comb_0 (x, y, z : message) : x = f(y) => y = f(z) => x = f(f(z)).
Proof.
  intro H1 H2; rewrite H1; rewrite H2; apply eq_refl.
Qed.

(* Simple goals can be proved automatically using the `auto` tactic.
   Actually, the previous goal could be proved directly with `auto`. *)
goal comb_1 (x, y, z : message) : x = f(y) => y = f(z) => x = f(f(z)).
Proof.
  auto.
Qed.

(* ----------------------------------------------------------------- *)
(* ----------------------------------------------------------------- *)
(** # BONUS  *)

(* ----------------------------------------------------------------- *)
(** ## Structuring proofs  *)

(* To improve readability, we often structure proofs using bullets,
   Exemples of bullet symbols are `-` and `*` (or repetition of those).
   Bullets are used when there are several subgoals, to separate the proof of
   each subgoals. *)
goal bonus_0 ['a] (b,b' : boolean, x,y : 'a):
  if b then (if b' then x else y) else y = if (b && b') then x else y.
Proof.
  case b.
  (* Open two subgoals (1) and (2), which we split with the bullet `-` *)

  - case b'.
   (* Split (1) between subgoals (1.1) and (1.2),
      which we split with bullet `*`. *)
    * auto.  (* concludes (1.1) *)
    * auto.  (* concludes (1.2) *)

  - case b'.
    (* Split (2) into (2.1) and (2.2).
       Again, we split them using `*`. *)
    * auto.  (* concludes (2.1) *)
    * auto.  (* concludes (2.2) *)
Qed.

(* Now, try to prove the previous goal in a single tactic,
   using the tactic `case` and `auto`, and the tactical `;`. *)
goal bonus_1 ['a] (b,b' : boolean, x,y : 'a):
  if b then (if b' then x else y) else y = if (b && b') then x else y.
Proof.
  admit. (* TODO *)
Qed.
