type int [well_founded, fix].

(*==================================================================*)
(* `Ordering` *)

(*------------------------------------------------------------------*)
(* `≤` *)

axiom [any] le_trans ['a] (x,y,z : 'a) : x <= y => y <= z => x <= z. 

(* holds for everybody but `timestamp`. *)
axiom [any] le_refl_i (i : int) : i <= i.
hint rewrite le_refl_i.

(* holds for everybody but `timestamp`. *)
axiom [any] le_linear_i (i,j : int) : i <= j || j <= i.

(*------------------------------------------------------------------*)
(* `<` *)

(* holds for everybody but `timestamp`. *)
axiom [any] lt_charac_i (i,j : int) : i < j <=> (i <> j && i <= j).

(* weaker version of `lt_charac_i` which also holds for timestamps *)
axiom [any] lt_impl_neq_le ['a] (x,y : 'a) : x < y => (x <> y || x <= y).

(*------------------------------------------------------------------*)
(* holds for everybody but `timestamp`. *)
axiom [any] le_charac_i (i,j : int) : i <= j <=> (i = j || i < j).

(* weaker version of `le_charac_i` which also holds for timestamps *)
axiom [any] le_impl_eq_lt ['a] (x,y : 'a) : x <= y => (x = y || x < y).

(*------------------------------------------------------------------*)
axiom [any] lt_impl_le ['a] (x,y : 'a) : x < y => x <= y.

(*------------------------------------------------------------------*)
(* holds for everybody but `timestamp`. *)
goal [any] lt_trans (x,y,z : int) : x < y => y < z => x < z. 
Proof.
  rewrite !lt_charac_i.
  intro [_ A] [_ B]. 
  split; 1: auto. 
  apply le_trans _ _ _ A B.
Qed.

(* holds for everybody but `timestamp`. *)
goal [any] lt_le_trans (x,y,z : int) : x < y => y <= z => x < z. 
Proof.
  rewrite !lt_charac_i.
  intro [_ A] B. 
  split; 1: auto. 
  apply le_trans _ _ _ A B.
Qed.

(* holds for everybody but `timestamp`. *)
goal [any] le_lt_trans (x,y,z : int) : x <= y => y < z => x < z. 
Proof.
  rewrite !lt_charac_i.
  intro A [_ B]. 
  split; 1: auto. 
  apply le_trans _ _ _ A B.
Qed.

(*------------------------------------------------------------------*)
axiom [any] lt_irefl ['a] (x : 'a) : x < x <=> false.

(*==================================================================*)
(* `Integers` *)

abstract i0 : int.
abstract i1 : int.

axiom [any] i0_min (i : int) : i0 <= i.
axiom [any] i0_lub (i : int) : i <= i0 <=> i = i0.

abstract (++) : int -> int -> int.
op succi (i : int) = i ++ i1.

axiom [any] succi_le (i : int) : i < succi i.
axiom [any] succi_le0 (i,j : int) : i < succi j <=> i <= j.

goal [any] not_lt_i0 (i : int) : not (i < i0).
Proof.
  intro A. 
  by rewrite lt_charac_i i0_lub in A. 
Qed.
