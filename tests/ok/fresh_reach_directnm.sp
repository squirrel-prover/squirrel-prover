name n : message
name m : message
abstract f : message->message

system null.

goal _: n = f(m) => False.
Proof.
  nosimpl(intro Heq).
  nosimpl(fresh Heq).
Qed.
