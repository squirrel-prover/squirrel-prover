include Core.

mutable s (i:index) : message = empty.
abstract f : index -> message.
mutable dummy : message = empty.

system !_i !_j diff(s(i),dummy) := diff(f(j),empty).

lemma [default/left] _ (i,j:_) : happens(A(i,j)) => s(i)@A(i,j) = f(j).
Proof.
  intro H.
  rewrite /s.
  by apply eq_refl.
Qed.

lemma [default/left] _ (i,j:_) : happens(A(i,j)) => dummy@A(i,j) = dummy@pred(A(i,j)).
Proof.
  intro H.
  rewrite /dummy.
  by apply eq_refl.
Qed.

lemma [default/right] _ (i,j:_) : happens(A(i,j)) => s(i)@A(i,j) = s(i)@pred(A(i,j)).
Proof.
  intro H.
  rewrite /s.
  by apply eq_refl.
Qed.

lemma [default/right] _ (i,j:_) : happens(A(i,j)) => dummy@A(i,j) = empty.
Proof.
  intro H.
  rewrite /dummy.
  by apply eq_refl.
Qed.
