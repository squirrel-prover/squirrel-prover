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

set debugConstr=true.
goal unforgeable_1 (a : index, b : index, c : index):
  happens (A(b)) => b <> a && c=a=>
  output@A(b) <> h(na(c),k).

Proof.
 nosimpl(intro Hap [H G] Hneq). rewrite -G in *. 
 expand output.
 collision. 
 auto.
Qed.
