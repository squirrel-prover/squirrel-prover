hash h
name k:message
name cst:message

channel c

name na : index -> message
name nb : index -> message
name nc : index -> message
name mc : index -> message
mutable s : message

system out(c,cst);
(
  (!_a out(c,<h(na(a),k),na(a)>))
  |  (in(c,m1); out(c,m1); in(c,m2); if m1=h(m2,k) then out(c,m2))
 ).

axiom name_not_pair :
forall (ma : message, mb : message, a:index),
na(a) <>  <ma, mb>.

goal unforgeable :
  forall (tau : timestamp, tau2:timestamp, b:index),
  input@A3=h(input@A,k) => exists (a:index), (input@A2 = na(a)).
  Proof.
  simpl.
  euf H.
  exists a1.
Qed.
