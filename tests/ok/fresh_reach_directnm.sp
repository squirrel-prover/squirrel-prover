name n : message
name m : message
abstract f : message->message

system null.

lemma _: n = f(m) => False.
Proof.
  nosimpl(intro Heq).
  nosimpl(fresh Heq).
Qed.
