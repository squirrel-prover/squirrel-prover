abstract ok : message
mutable s : message
channel c
axiom init_ok : s@init = ok
system !_i in(c,x);s:=s;out(c,x).

goal forall t:timestamp, s@t = ok.
Proof.
  induction.
  case t.
  case H0.
  (* t = A(i) *)
  apply IH0 to pred(A(i)).
  (* t = init *)
  apply init_ok.
Qed.