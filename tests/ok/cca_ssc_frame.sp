aenc enc, dec, pk.
senc sym_enc,sym_dec.

name sk : message.

name n : message.
name eta : message.

lemma [any] len_n : len(n) = len(eta).
Proof. by rewrite namelength_n namelength_eta. Qed.

channel c.

process P =
  new r;
  out(c, enc(diff(n,zeroes(eta)),r,pk(sk))).


system S = P.

include Core.

global lemma [S] ideal (t:timestamp[const]) :
  [happens(t)] ->
  equiv(frame@t, sk, eta).
Proof.
 induction t; intro Hap.
 + auto.
 + rewrite /frame /output /exec /cond.
   fa !<_,_>, (if _ then _).
   (* cca1 does not conclude because of sk *)
   checkfail (by cca1 1) exn GoalNotClosed.
Abort.
