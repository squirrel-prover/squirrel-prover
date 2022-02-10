set autoIntro=false.

channel c.
system !_i R: in(c,x); out(c,x).

goal _ (x,y : message) : x = y => x = y.
Proof.
 intro H. 
 assumption.
Qed.

goal _ (x,y : message) : x = y => True.
Proof.
 intro H. 
 assumption.
Qed.

goal _ (x,y : message) : False => x = y.
Proof.
 intro H. 
 assumption.
Qed.

goal _ (i:index,t:timestamp) : 
happens(t) => R(i) <> t.
Proof.
 checkfail (intro H; auto) exn GoalNotClosed.
Abort.

