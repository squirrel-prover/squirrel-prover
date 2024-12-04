namespace N. 
  game G = {
    oracle f = { return diff(0,1); }
  }.
end N.

system P = null.

global lemma _ @system:P : equiv(diff(0,1)). 
Proof. 
  crypto N.G.
Qed.
