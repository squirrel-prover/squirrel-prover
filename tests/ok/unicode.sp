op 🐇 = empty.

axiom [any] 🌶 (🐶 : message) : 🐶 = 🐇.

op (⊳) x y = <x,y>.

lemma [any] _ 🐶 : 🐇 ⊳ 🐶 = 🐶 ⊳ 🐇.
Proof.
  rewrite /(⊳).
  rewrite (🌶 🐶). 
  auto.
Qed.

op (⊳=>) x y = <x,y>.

lemma [any] _ 🐶 : 🐇 ⊳ 🐶 = 🐶 ⊳=> 🐇.
Proof.
  rewrite /(⊳).
  rewrite (🌶 🐶). 
  auto.
Qed.
