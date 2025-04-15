channel c.


hash h.
senc enc, dec where k : message.

abstract ok : message.
name k : message.
name r :  message.

mutable m : message = empty.

system S = 
  A : out(c, enc(ok, r, k)) | B : out(c, h(ok, k)).

lemma [S] _ : dec(output@A,k)<>fail => false.
Proof.
  intro H.
  intctxt H.  (* there should be two possible occurences, as we can't unfold output. *)
  assert (B <= A => false ) by admit.
  assumption.
  assert (A <= A && output@A = enc (ok, r, k) => false ) by admit.
  assumption.
Qed.
