set autoIntro=false.

name n : message
name m : message
abstract f : message->message

system null.

goal n = f(m) => False.
Proof.
  nosimpl(intro Heq).
  nosimpl(fresh Heq).
  by auto.
Qed.
