name n : message
name m : message
abstract f : message->message
channel c
system out(c,m).

goal forall tau:timestamp, n = f(frame@tau) => False.
Proof.
  nosimpl(intros).
  nosimpl(fresh M0).
  nosimpl(false_left).
Qed.
