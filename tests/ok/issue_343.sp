namespace Basic.

  name k : message.

  print namelength_message.
  print namelength_k.

  axiom [any] _ : namelength_message = namelength_message.

end Basic.

print namelength_k.       (* -> not found *)
print Basic.namelength_k. (* -> found *)

print namelength_message. (* -> found *)
axiom [any] _ : namelength_message = namelength_message.

name key : message.

lemma [any] _ : len key = len Basic.k.
Proof. rewrite namelength_key. rewrite Basic.namelength_k. auto. Qed.
