set autoIntro=false.

system null.

goal fst_pair (x,y : message) : fst (<x,y>) = x.
Proof. auto. Qed.

goal snd_pair (x,y : message) : snd (<x,y>) = y.
Proof. auto. Qed.

hint rewrite fst_pair.
hint rewrite snd_pair.

goal _ (a,b,c : message) : a = c => fst(<a,b>) = c.
Proof. 
 intro H.
 simpl.
 assumption.
Qed.

goal _ (a,b,c : message) : a = c => fst(<b,a>) = c.
Proof. 
 intro H.
 simpl.
 checkfail auto exn GoalNotClosed.
Abort.

goal _ (a,b,c : message) : a = c => fst(snd(<b, <a,b>>)) = c.
Proof. 
 intro H.
 simpl.
 assumption.
Qed.

