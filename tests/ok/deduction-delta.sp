include Core.
include WeakSecrecy.

system null.

global lemma _ (u1,u2:message):
  Let v = (u1,u2) in
  $((u1,u2) |>( v)). 
Proof.
  intro ?.
  deduce ~all.
Qed.

global lemma _ (u1,u2:message):
  Let v = (u1,u2) in
  $((v) |>(u1,u2)). 
Proof.
  intro ?.
  deduce ~all.
Qed.
