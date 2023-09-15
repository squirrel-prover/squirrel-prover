include Basic.

name n : index -> message.

mutable s (i : index) = n i.

abstract i0 : index.

channel c.

(* -------------------------------------------------- *)
process A0 i j = s (i) := empty; A1: out (c,< n i, n j>).

system [P0] !_i !_j A0(i,i).
print system [P0].

(* check that [s] is well-formed *)
lemma [P0] _ (i0, i1, j : index) : 
  happens (A1 (i0,i1)) => 
  s j@A1 (i0,i1) = 
  if j = i0 then 
    empty 
  else 
    s(j)@pred (A1 (i0,i1)).
Proof.
  intro Hap.
  rewrite /s.
  apply eq_refl.
Qed.

(* -------------------------------------------------- *)
process A j y = out (c,< n j, y>).

system [P] A(i0, empty).
print system [P].

(* -------------------------------------------------- *)
abstract f : message -> message.

process A1 (j : index) =
  s(j) := f(s j); A2: out (c,empty).

(* instanciate A1 on the constant `i0` *)
system [P1] !_i A1: A1(i0).
print system [P1].

(* check that [s] is well-formed *)
lemma [P1] _ (i, j : index) : 
  happens (A2 i) => 
  s j@A2 i = 
  if j = i0 then 
    f (s(j)@pred (A2 i))
  else 
    s(j)@pred (A2 i).
Proof.
  intro Hap.
  rewrite /s.
  by fa. 
Qed.

(* -------------------------------------------------- *)
(* instanciate A1 on the replication variable `i` *)
system [P1bis] !_i A1: A1(i).
print system [P1].

(* check that [s] is well-formed *)
lemma [P1bis] _ (i, j : index) : 
  happens (A2 i) => 
  s j@A2 i = 
  if j = i then 
    f (s(j)@pred (A2 i))
  else 
    s(j)@pred (A2 i).
Proof.
  intro Hap.
  rewrite /s.
  by fa.
Qed.

(* -------------------------------------------------- *)
(* we use a constant index when updating the state *)
process A2 (j : index) =
  s(i0) := f(s i0).

system [P2] !_i A2(i).
print system [P2].

(* check that [s] is well-formed *)
lemma [P2] _ (i, j : index) : 
  happens (A2 i) => 
  s j@A2 i = 
  if j = i0 then 
    f (s(j)@pred (A2 i))
  else 
    s(j)@pred (A2 i).
Proof.
  intro Hap.
  rewrite /s.
  by fa.
Qed.


