(*******************************************************************************
# Reasoning with names

This file shows how to declare names and reason about freshness.
*******************************************************************************)

(* Please ignore the two lines of setup. *)
include Logic.
system null.

(* We declare a few names. *)
name n : message.
name m : message.

(* Recall that names represent uniform random samplings of length
   the security parameter.
   Distinct name symbols are independent random samplings.
   Consequently, the probability of two distinct names being equal is
   negligible. This can be proved using the `fresh` tactic. *)
lemma fresh_0 : n = m => false.
Proof.
  intro Eq.
  fresh Eq.
Qed.

(* We can have indexed families of names. *)
name n1 : index -> message.
name m1 : index -> message.

(* The fresh tactic handles indices gently. *)
lemma fresh_1 : forall (i,j:index), n1 i = n1 j => j = i.
Proof.
  intro i j Eq.
  fresh Eq.
  auto.
Qed.

(* Two names `n1(i)` and `n1(j)` represent the same random sampling
   if and only if they have the same indices. *)
lemma exo_1 (i, j : index) : n1(i) = n1(j) => i = j.
Proof.
  admit. (* TODO *)
Qed.

(* Names `n1(i)` and `m2(j)` never represent the same random sampling. *)
lemma exo_2 (i : index) : n1(i) = m1(i) => false.
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
lemma exo_3 (i0, i1, i2, j : index) :
  <n1(i0), <m1(i1), n1(i2)>> = n1(j) =>
  (j = i0 || j = i2).
Proof.
  admit. (* TODO *)
Qed.
