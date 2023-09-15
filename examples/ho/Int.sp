(* Theory of integers *)

(* This theory must be loaded after `Basic`. *)

type int [well_founded, fixed].

(*==================================================================*)
(* `Ordering` *)

(*------------------------------------------------------------------*)
(* `≤` *)

(* Holds for every type but `timestamp`. *)
axiom [any] le_refl_i (i : int) : i <= i.
hint rewrite le_refl_i.

(* Holds for every type but `timestamp`. *)
axiom [any] le_linear_i (i,j : int) : i <= j || j <= i.

(* Holds for every type but `timestamp`. *)
axiom [any] le_charac_i (i,j : int) : i <= j <=> (i = j || i < j).

(*==================================================================*)
(* `Integers` *)

(* Zero and one *)
abstract i0 : int.
abstract i1 : int.

axiom [any] i0_lub (i : int) : i <= i0 <=> i = i0.

lemma [any] i0_min (i : int) : i0 <= i.
Proof.
  have [H|H] := le_linear_i i0 i.
  + assumption.
  + rewrite (i0_lub i) in H.
    rewrite H.
    apply le_refl_i.
Qed.

lemma [any] not_lt_i0 (i : int) : not (i < i0).
Proof.
  intro A.
  by rewrite lt_charac i0_lub in A.
Qed.

(* Addition and successor *)
abstract (++) : int -> int -> int.
op succi (i : int) = i ++ i1.

axiom [any] succi_le (i : int) : i < succi i.
axiom [any] succi_le0 (i,j : int) : i < succi j <=> i <= j.

lemma [any] lt_succ (i, j : int) :
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
