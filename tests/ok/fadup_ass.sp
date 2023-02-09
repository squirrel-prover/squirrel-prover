name a : message
name b : message
channel c
system !_i in(c,x);out(c,x).

equiv test (t:timestamp[const]) : diff(input@t,a), diff(input@t,b).
Proof.
  (* Induction is only here to introduce an equivalence hypothesis. *)
  induction t.
  admit.
  enrich diff(input@pred(A(i)),a).
  nosimpl(admit 1; admit 1).
  nosimpl(fadup).
  assumption.
Qed.
