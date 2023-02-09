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


goal dummy (tau1 : timestamp, tau2 : timestamp, a : index, b: message) :
  tau1 = tau2 =>
  output@tau1= output@tau2.
Proof.
 auto.
Qed.

goal unforgeable_1 (a : index, b : index) :
 happens(A(b)) => 
  b <> a =>
  output@A(b) <> h(na(a),k).

Proof.
 intro Hap Hneq Heq.
 expand output.
 collision.  
 auto.
Qed.

goal unforgeable_2 (a, b : index[glob]):
 happens(B(b)) => 
  output@B(b) <> h(na(a),k).
Proof.
 intro Hap Heq.
 expand output.
 nosimpl(collision).
 nosimpl(intro Heq2).
 by fresh Heq2.
Qed.


goal unforgeable_3 (a, b: index[glob]):
 happens(C(b)) => 
  output@C(b) <> h(na(a),k).

Proof.
 intro Hap Heq.
 expand output.
 collision. 
 intro Heq2.
 by fresh Heq2. 
Qed.
