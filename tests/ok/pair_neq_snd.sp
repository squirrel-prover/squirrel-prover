set autoIntro=false.

system null.

axiom pair_neq_snd :
  forall (x:message, y:message),
  <x,y> <> y

axiom pair_eq_snd_absurd :
  forall (x:message, y:message),
  <x,y> = y => False.

goal _ (x,y:message): <x,y> = y => False.
Proof.
  intro x y Heq.
  by use pair_neq_snd with x,y.
Qed.

goal _ (x,y:message): <x,y> <> y.
Proof.
  intro x y Heq.
  by use pair_neq_snd with x,y.
Qed.

goal _ (x,y:message): <x,y> = y => False.
Proof.
  intro x y Heq.
  by use pair_eq_snd_absurd with x,y.
Qed.

goal _ (x,y:message): <x,y> <> y.
Proof.
  intro x y Heq.
  by use pair_eq_snd_absurd with x,y.
Qed.
