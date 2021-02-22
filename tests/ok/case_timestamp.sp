set autoIntro=false.

channel c

system (in(c,x);out(c,x) | !_i in(c,x);out(c,x)).

goal _ (t:timestamp) :
  t = init || (t = A || exists i:index, t = A1(i)).
Proof.
  intro tau. 
  case tau.  
  by left. 
  by right; left. 
  by right; right. 
Qed.
