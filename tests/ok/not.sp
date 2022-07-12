system null.
goal _ (t:timestamp): not(happens(t)) => not(happens(t)).
Proof.
  nosimpl(intro Hnot H).
  nosimpl(use Hnot; assumption). 
Qed.
