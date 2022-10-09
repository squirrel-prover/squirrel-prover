name n : message
name m : message
abstract f : message->message
channel c
system out(c,m).

goal _ (tau:timestamp): happens(tau) => n = f(frame@tau) => False.
Proof.
  nosimpl(intro Hap Heq).
  nosimpl(fresh Heq).
Qed.
