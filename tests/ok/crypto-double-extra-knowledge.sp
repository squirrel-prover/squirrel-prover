include Core.


(** This tests stands to verify that free vars in extra-outputs computed in the fisrt passes is forward to the extra inputs *)

abstract a:message.
abstract format : (index -> message) -> message.

game RD = {
  oracle random = {
  rnd r:message;
  return diff(r,a)}
}.

name n : index -> message .

channel c.

process A = 
 out(c, format (fun i => diff(n(i),a))).

process B (i:index) = 
 out(c,diff(n(i),a)).

system foo = A | !_i B i.

(* set verboseCrypto = true. *)

global lemma [foo] _ (t:timestamp[const]):
[happens(t)] -> equiv(frame@t).
Proof.
intro Hap.
crypto RD.
* auto.
* intro *.
  destruct H as [h0 h1 h2 h3].
  rewrite Ieq in *.
  assert (A < B(i0))||(B(i0) < A). constraints.
  by case H.
* intro *.
  destruct H as [h0 h1 h2 h3].
  auto.
Qed.

name m : message.

process Abis = 
  out(c,format (fun i=> diff(m,a))).

process Bbis (i:index) = 
  out(c,diff(m,a)).

system foobis = Abis | (!_i Bbis(i)).

global lemma [foobis] _ (t:timestamp[const]):
[happens(t)] -> equiv(frame@t).
Proof.
intro Hap.
crypto RD.
* intro *.
  destruct H as [[h0 h1] h2 [h3 h4] h5].
  have hi := h3 i.
  have hi0 := h0 i0.
  rewrite h2 h5 in *.
  simpl.
  assert (B(i) < B(i0) || B(i0) < B(i)) by constraints.
  by case H.  
* intro *.
  destruct H as [[h0 h1] h2 [h3 h4] h5].
  have hi := h4 i.
  rewrite h2 in hi.
  rewrite h5 in h1.
  assert (B(i) < A || A < B(i)) by constraints.
  by case H.  
* intro *.
  destruct H as [[h0 h1] h2 [h3 h4] h5].
  rewrite h1 h5 in *.
  rewrite forall_true1 in *.
  simpl.
  clear h1.
  assert exists m, forall (i:index), m <= i.
  admit.
  destruct H as [m h].
  have hi := h i.
  have hi0 := h i0.
  simpl.
  have hmi := h0 m.  
  have hmi0 := h3 m.
  assert m = i by apply le_not_lt_impl_eq.
  assert m = i0 by apply le_not_lt_impl_eq. 
  constraints.
Qed.
