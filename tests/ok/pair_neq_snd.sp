system null.

axiom pair_neq_snd (x:message, y:message):
  <x,y> <> y

axiom pair_eq_snd_absurd (x:message, y:message):
  <x,y> = y => False.

lemma _ (x,y:message): <x,y> = y => False.
Proof.
  intro Heq.
  by use pair_neq_snd with x,y.
Qed.

lemma _ (x,y:message): <x,y> <> y.
Proof.
  intro Heq.
  by use pair_neq_snd with x,y.
Qed.

lemma _ (x,y:message): <x,y> = y => False.
Proof.
  intro Heq.
  by use pair_eq_snd_absurd with x,y.
Qed.

lemma _ (x,y:message): <x,y> <> y.
Proof.
  intro Heq.
  by use pair_eq_snd_absurd with x,y.
Qed.
