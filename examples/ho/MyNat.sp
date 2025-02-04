(* Theory of integers *)

include Core.

type nat[well_founded, serializable, fixed].

(*==================================================================*)
(* `Ordering` *)

(*------------------------------------------------------------------*)
(* `≤` *)

(* Holds for every type but `timestamp`. *)
axiom [any] le_refl_i (i : nat) : i <= i <: Real.z.
hint rewrite le_refl_i.

(* Holds for every type but `timestamp`. *)
axiom [any] le_linear_i (i,j : nat) : i <= j || j <= i.

(* Holds for every type but `timestamp`. *)
axiom [any] le_charac_i (i,j : nat) : i <= j <=> (i = j || i < j).

(*==================================================================*)
(* `Integers` *)

(* Zero and one *)
abstract i0 : nat.
abstract i1 : nat.

axiom [any] i0_lub (i : nat) : i <= i0 <=> i = i0.

lemma [any] i0_min (i : nat) : i0 <= i.
Proof.
  have [H|H] := le_linear_i i0 i.
  + assumption.
  + rewrite (i0_lub i) in H.
    rewrite H.
    apply le_refl_i.
Qed.

lemma [any] not_lt_i0 (i : nat) : not (i < i0).
Proof.
  intro A.
  by rewrite lt_charac i0_lub in A.
Qed.

(* Addition and successor *)
abstract (++) : nat -> nat -> nat.
op succi (i : nat) = i ++ i1.

axiom [any] succi_le (i : nat) : i < succi i.
axiom [any] succi_le0 (i,j : nat) : i < succi j <=> i <= j.

lemma [any] lt_succ (i, j : nat) :
  (i < succi j) <=>
  (i <> succi j && i <= succi j).
Proof.
  split.
  + intro H.
    split; 1:auto.
    by apply lt_impl_le.
  + intro [H1 H2].
    apply le_impl_eq_lt in H2.
    by case H2.
Qed.
