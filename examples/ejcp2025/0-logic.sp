(***********************************************************************
# Basic Logical Reasoning

This file introduces, through a series of simple exercices, the core
tactics allowing to do basic logical reasoning in Squirrel.

Because the objective is do a quick overview of the logical tactics
in Squirrel, the lemmas below are most of the time trivial.

The syntax for tactics is often inspired from the Coq proof assistant.
Consequently, users familiar with Coq should be able to quickly go
through this file.
***********************************************************************)

(** Basic setup: this can be ignored. *)
include Logic.
system null.

(* ----------------------------------------------------------------- *)
(** ## A first few simple lemmas *)

(** In this example, we use a boolean as a proposition:
    it says that if boolean b1 is true, then if boolean b2 is true,
    then boolean b1 && b2 (conjunction) is also true. *)
lemma basic_0 : forall (b1, b2 : bool), b1 => b2 => (b1 && b2).
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

lemma basic_1 : forall (b1, b2 : bool), (b1 && b2) => (b2 && b1).
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

lemma basic_2 :
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

lemma basic_3 :
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

lemma disj_0 : forall (b1,b2:bool), (b1 || b2) => (b2 || b1).
Proof.
  intro b1 b2 H.
  (* We use case to perform a case analysis
     on a disjunctive assumption, which yields 
     two sub-lemmas. *)
  case H.

  (* -- First sub-lemma -- *)
  (* The conclusion is a disjunction,
     we prove it by selecting the right disjunct. *)
  right.
  apply H.

  (* -- Second sub-lemma -- *)
  left.
  apply H.
Qed.

lemma disj_1 : forall (b1,b2,c:bool),
  (b1 && b2) => ((b1=>c) || (b2=>c)) => c.
Proof.
  admit. (* TODO *)
Qed.

(* ----------------------------------------------------------------- *)
(** ## Rewriting *)

(* Variables `x, y` are introduced by default, because they are
   described before the colon `:`. *)
lemma rewrite_0 (x, y, z : message) : x = y => y = z => x = z.
Proof.
  intro H1 H2.

  (* An equality hypothesis `H : u = v` can be used to replace
     occurrences of `u` by `v`, using `rewrite H`. *)
  rewrite H1.
  rewrite H2.

  (* To conclude, we can use the `eq_refl` lemma, which is part of the
     standard library.
     You can print the lemma's statement using `print`. *)
  print eq_refl.
  apply eq_refl.
Qed.

(* We declare an abstract (i.e. unspecified) predicate `P` over booleans. *)
abstract P : message -> bool.

lemma rewrite_1 (x, y : message) : x = y => P(x) => P(y).
Proof.
  intro Heq Hp.

  (* `rewrite` only rewrites in the lemma. To rewrite in another
     hypothesis, we can use `rewrite _ in _`. *)
  rewrite Heq in Hp.
  apply Hp.
Qed.

lemma rewrite_2 (x, y : message) : (P(y) || y = x) => P(x) => P(y).
Proof.
  admit. (* TODO *)
Qed.

(* ----------------------------------------------------------------- *)
(** ## Existential quantifier *)

(* We first declare a few function symbols, with their types. *)
abstract f : message -> message.
abstract g : message -> message.

lemma exists_0 (x, z : message) :
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
lemma exists_1 (x, z : message) :
  (exists (y : message), x = y && y = z) =>
  x = z.
Proof.
  admit. (* TODO *)
Qed.

(* To prove an existential, we can use the `exists y` tactic
   (where `y` is the witness). *)
lemma exists_2 (x : message) :
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
lemma exists_3 (x, z : message) :
  (exists (y : message), x = f(y)) =>
  (exists (y : message), f(y) = x).
Proof.
  admit. (* TODO *)
Qed.

(* ----------------------------------------------------------------- *)
(** ## Introducing intermediate lemmas with `have` *)

lemma have_1 (x : message) :
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

lemma have_2 (x, y : message) :
  (forall (z : message), z = x || P(z)) =>
  P(x) =>
  P(y).
Proof.
  admit. (* TODO *)
Qed.

(* ----------------------------------------------------------------- *)
(** ## Automation *)

(* Simple lemmas can be proved automatically using the `auto` tactic.
   For example, the next lemma can be proved directly with `auto`. *)
lemma comb_1 (x, y, z : message) : x = f(y) => y = f(z) => x = f(f(z)).
Proof.
  auto.
Qed.

(* The smt tactic, if available, is (in general) even more powerful than
   auto. But it does not perform any cryptographic reasoning.
   Try it whenever a goal seems "obvious" but tedious to prove step by step. *)

(* ----------------------------------------------------------------- *)
(** ## Structuring proofs  *)

(* To improve readability, we often structure proofs using bullets.
   Examples of bullet symbols are `-` and `*` (or repetition of those).
   Bullets are used when there are several sub-goals, to separate the proof of
   each sub-goal. Using bullets is HIGHLY RECOMMENDED for the tutorials,
   and even more so for large proofs. *)
lemma bonus_0 ['a] (b,b' : boolean, x,y : 'a):
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

(* ----------------------------------------------------------------- *)
(* ----------------------------------------------------------------- *)
(** # BONUS  *)

(* ----------------------------------------------------------------- *)
(** ## Combining tactics *)

(* Tactics can be composed using `;`:
   `tac1; tac2` applies the tactic `tac1`, and then
   applies `tac2` to all subgoals produced by `tac1`. *)

(* E.g. the following lemma can be proved with a single tactic. *)
lemma comb_0 (x, y, z : message) : x = f(y) => y = f(z) => x = f(f(z)).
Proof.
  intro H1 H2; rewrite H1; rewrite H2; apply eq_refl.
Qed.

(* Now, try to prove the previous lemma in a single tactic,
   using the tactic `case` and `auto`, and the tactical `;`. *)
lemma bonus_1 ['a] (b,b' : boolean, x,y : 'a):
  if b then (if b' then x else y) else y = if (b && b') then x else y.
Proof.
  admit. (* TODO *)
Qed.
