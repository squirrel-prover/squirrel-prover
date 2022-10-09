name n : index -> message
abstract f : message * message -> message

system null.

goal _ (i1,i2,j:index): n(j) = f(n(i1),n(i2)) => (j = i1 || j = i2).
Proof.
intro Heq.
fresh Heq; intro H.
by left.
by right.
Qed.
