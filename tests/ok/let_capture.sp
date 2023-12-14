channel c.

process foo = 
  (* let x = zero in *)
  out(c,empty).

system (F :foo).

global lemma _ : 
  Let x = empty in equiv(x).
Proof.
  intro *.
  rewrite /x.
Abort.

global lemma _ (x : message) : 
  Let x = empty in equiv(x).
Proof.
  intro *.
  rewrite /x0.
Abort.
