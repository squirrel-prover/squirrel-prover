

hash h
name k:message
name cst:message

channel ch

name na : index -> message
name nb : index -> message
name nc : index -> message
name mc : index -> message


system O: out(ch,cst); out(ch,k); (
    (A: !_a out(ch,h(na(a),k)))
  | (B: !_b out(ch,h(<nb(b),nb(b)>,k)))
  | (C: !_c out(ch,h(<nc(c),mc(c)>,k)))
).

axiom name_not_pair (ma : message, mb : message, a:index):
na(a) <>  <ma, mb>.

goal unforgeable_1 :
  forall (a : index, b : index),
  b <> a =>
  output@A(b) <> h(na(a),k).

Proof.
  checkfail collision exn NoSSC.
Abort.
