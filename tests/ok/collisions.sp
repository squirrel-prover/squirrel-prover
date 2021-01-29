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


goal dummy :
  forall (tau1 : timestamp, tau2 : timestamp, a : index, b: message),
  tau1 = tau2 =>
  output@tau1= output@tau2.
Proof.
 by auto.
Qed.

goal unforgeable_1 :
  forall (a : index, b : index),
  b <> a =>
  output@A(b) <> h(na(a),k).

Proof.
 intro a b Hneq Heq.
 collision.  
 by auto.
Qed.

goal unforgeable_2 :
  forall (a : index, b : index),
  output@B(b) <> h(na(a),k).

Proof.
 intro a b Heq.
 nosimpl(collision).
 nosimpl(intro Heq2).
 eqnames.
Qed.


goal unforgeable_3 :
  forall (a : index, b : index),
  output@C(b) <> h(na(a),k).

Proof.
 intro a b Heq.
 collision. 
 intro Heq2. 
 case Ieq. 
Qed.
