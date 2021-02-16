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
  apply pair_neq_snd to x,y.
Qed.

goal _ (x,y:message): <x,y> <> y.
Proof.
  intro x y Heq.
  apply pair_neq_snd to x,y.
Qed.

goal _ (x,y:message): <x,y> = y => False.
Proof.
  intro x y Heq.
  apply pair_eq_snd_absurd to x,y.
Qed.

goal _ (x,y:message): <x,y> <> y.
Proof.
  intro x y Heq.
  apply pair_eq_snd_absurd to x,y.
Qed.
