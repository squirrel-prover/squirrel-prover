channel c.

system K : out(c,empty).

global lemma _ (t : timestamp, x,y:message) :
  [happens(t)] ->
  [pred t = K] ->
  [t = K] ->
  equiv(diff(x,y)).
Proof. intro ???. constraints. Qed.
