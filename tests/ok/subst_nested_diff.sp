include Core.

system P = null.

global lemma _ @system:P :
Let i_01 = diff(0,1) in
Let i_23 = diff(2,3) in
Let a = diff(i_01,i_01) in
Let b = diff(i_01,i_23) in
Let c = diff(i_23,i_01) in
Let d = diff(i_23,i_23) in
[
  a = diff(0,1) && 
  b = diff(0,3) && 
  c = diff(2,1) && 
  d = diff(2,3)
].
Proof. 
simpl. 
true.
Qed.

global lemma _ @system:P (y :message) :
[ diff(y, y) = witness ]
-> 
[
  (fun x => diff(x, x)) (diff(y, y))
  =
  witness
].
Proof.
  intro H. 
  reduce ~beta. 
  assumption H.
Qed.
