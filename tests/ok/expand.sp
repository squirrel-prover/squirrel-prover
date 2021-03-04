set autoIntro=false.
(* set debugConstr=true. *)

channel c

abstract ok : index -> message
abstract ko : index -> message
abstract b : message
abstract d : message

system ((B: !_j in(c,x); if x = ok(j) then out(c,<x,ok(j)>)) |
        (C: !_j in(c,x); if x = ko(j) then out(c,<x,ko(j)>))).

goal _ (t, t', t'' : timestamp, i, j: index) :
  happens(t,t') => t = B(i) => t' = C(j) => 
  (<input@B(i),ok(i)> = b =>
   <input@B(i),ok(i)> = d =>
   <input@C(j),ko(j)> = b => (output@t'' = b => <input@B(i),ok(i)> = ok(i))) =>
  output@t = b =>
  output@t = d =>
  output@t' = b => 
  output@t'' = b => 
  output@t = ok(i).
Proof.
  intro t t' t'' i j H Teq Teq1 Assum H0.
  expand output.
  revert H0.
  assumption.
Qed.

(* Same, but choosing the expand timestamps manually *)
goal _ (t, t', t'' : timestamp, i, j: index) :
  happens(t,t') => t = B(i) => t' = C(j) => 
  (<input@B(i),ok(i)> = b =>
   <input@B(i),ok(i)> = d =>
   <input@C(j),ko(j)> = b => (output@t'' = b => <input@B(i),ok(i)> = ok(i))) =>
  output@t = b =>
  output@t = d =>
  output@t' = b => 
  output@t'' = b => 
  output@t = ok(i).
Proof.
  intro t t' t'' i j H Teq Teq1 Assum H0.
  expand output@t, output@t'.
  revert H0.
  assumption.
Qed.

(* Same, but expanding only one timestamp *)
goal _ (t, t', t'' : timestamp, i, j: index) :
  happens(t,t') => t = B(i) => t' = C(j) => 
  (<input@B(i),ok(i)> = b =>
   <input@B(i),ok(i)> = d =>
   output@t' = b => (output@t'' = b => <input@B(i),ok(i)> = ok(i))) =>
  output@t = b =>
  output@t = d =>
  output@t' = b => 
  output@t'' = b => 
  output@t = ok(i).
Proof.
  intro t t' t'' i j H Teq Teq1 Assum H0.
  expand output@t.
  revert H0.
  assumption.
Qed.
