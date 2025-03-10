include Core.

channel c.

system (
    out(c,empty)
).


game G = { }.

global lemma _ (t:timestamp[const]) : equiv(empty).
Proof.
  rewrite /*. 
  crypto G.
Qed.
