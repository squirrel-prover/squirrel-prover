

hash h
name k : message
name n1 : message
name n2 : message
name m : message

system null.

lemma function_right : h(m,k) <> n1 XOR n2.

Proof.
  intro Heq.
  euf Heq.
Qed.

lemma function_left : n1 XOR n2 <> h(m,k).

Proof.
  intro Heq.
  euf Heq.
Qed.
