abstract ok : message
mutable s : message
channel c
system !_i in(c,x);s:=s;out(c,x).

axiom init_ok : s@init = ok.

goal forall t:timestamp, s@t = ok.
Proof.
  induction.
  intro Hind.
  case t. intro H.
  case H.
  (* t = init *)
  apply init_ok. 
  
  (* t = A(i) *) 
  apply Hind to pred(A(i)). 
Qed.
