axiom pair_neq_snd :
  forall (x:message, y:message),
  <x,y> <> y

axiom pair_eq_snd_absurd :
  forall (x:message, y:message),
  <x,y> = y => False

system null.

goal forall (x,y:message), <x,y> = y => False.
Proof.
  intros.
  apply pair_neq_snd to x,y.
Qed.

goal forall (x,y:message), <x,y> <> y.
Proof.
  intros.
  apply pair_neq_snd to x,y.
Qed.

goal forall (x,y:message), <x,y> = y => False.
Proof.
  intros.
  apply pair_eq_snd_absurd to x,y.
Qed.

goal forall (x,y:message), <x,y> <> y.
Proof.
  intros.
  apply pair_eq_snd_absurd to x,y.
Qed.
