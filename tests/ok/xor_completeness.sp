abstract f : message -> message
abstract ff : message * message -> message

system null.

lemma _ (x,y,z:message):
  x = xor y z => xor y x = z.
Proof.
auto.
Qed.

lemma _ (a,x,y,z:message):
  a = xor x (f(ff(snd(y),f(z))))
  =>
  xor a x = f(ff(snd(y),f(z))).
Proof.
auto.
Qed.

lemma _ (a,x,y,z:message):
  a = xor x (f(xor (snd y) (f z)))
  =>
  xor a x = f(xor(snd y) (f z)).
Proof.
auto.
Qed.
