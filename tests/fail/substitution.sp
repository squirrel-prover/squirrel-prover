

hash h
name k:message
name cst:message

channel ch

name na : index -> message
name nb : index -> message
name nc : index -> message
name mc : index -> message

system O: out(ch,cst); (
    (A: !_a out(ch,h(na(a),k)))
  | (B: !_b out(ch,h(<nb(b),nb(b)>,k)))
  | (C: !_c out(ch,h(<nc(c),mc(c)>,k)))
).

goal unforgeable_1 :
  forall (a : index, b : index, c : index),
  b <> a && c=a=>
  output@A(b) <> h(na(c),k).

Proof.
 nosimpl(intro a b c H).
 checkfail subst a, b exn NotEqualArguments.
Abort.
