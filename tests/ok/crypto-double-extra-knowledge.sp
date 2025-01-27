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

set verboseCrypto = true.

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
