abstract ok : message
mutable s : message
channel c
system !_i in(c,x);s:=s;out(c,x).

axiom init_ok : s@init = ok.

goal forall t:timestamp, s@t = ok.
Proof.
  induction.
  case t.
  case H0.
  (* t = init *)
  apply init_ok.
  (* t = A(i) *)
  apply IH0 to pred(A(i)).
Qed.
