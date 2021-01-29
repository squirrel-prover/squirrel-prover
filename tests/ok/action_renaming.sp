abstract ok : index->message
channel c

system A: !_i in(c,x);out(c,<ok(i),x>).

goal one : forall k:index, output@A(k) = <ok(k),input@A(k)>.
Proof.
  auto.
Qed.

system [alt] B: !_j in(c,x); if x = ok(j) then out(c,<x,ok(j)>).

goal [none,alt] two : forall k:index, output@A(k) = <input@A(k),ok(k)>.
Proof.
  auto.
Qed.

goal [none,alt] three : forall k:index, cond@A(k) => input@A(k) = ok(k).
Proof.
  intro k Cond; expand cond@A(k).
Qed.
