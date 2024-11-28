include Core.

channel c.

system A = in(c,x);out(c,x).
system B = in(c,y);out(c,y).

global lemma [A/left,B/left] _ (tau:timestamp[const]) :
  [happens(tau)] -> equiv(frame@tau).
Proof.
  intro Hap.
  induction tau.
  + auto. 
  + expandall. apply IH.
Qed.
