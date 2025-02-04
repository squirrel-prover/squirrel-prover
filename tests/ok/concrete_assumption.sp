 channel c.
system !_i R: in(c,x); out(c,x).

lemma _ (x,y : message) : x = y => x = y <: Real.z.
Proof.
 intro H.
 assumption H.
Qed.

lemma _ (x,y : message) : x = y => x = y <: Real.z.
Proof.
 intro H.
 assumption.
Qed.

include Real.

lemma _ (x,y : message) : x = y => x = y <: Real.opp (Real.of_int 2).
Proof.
 intro H.
 checkfail assumption exn NotHypothesis.
Abort.

lemma _ (x,y : message) : x = y => x = y <: Real.opp (Real.z).
Proof.
 intro H.
 assumption.
Qed.

lemma _ (x,y : message) : x = y => x = y <: Real.opp (Real.opp (Real.of_int 2)).
Proof.
 intro H.
 assumption.
Qed.

lemma _ (x,y,z : message) : x = y => x = z => x = y <: Real.of_int 12.
Proof.
 intro H H'.
 checkfail assumption H' exn NotHypothesis.
 checkfail assumption H exn NotHypothesis.
 assumption.
Qed.

lemma _ (x,y : message) : x = y => True <: Real.of_int 12.
Proof.
 intro H.
 assumption.
Qed.

lemma _ (x,y : message) : x = y => True <: Real.opp (Real.of_int 12).
Proof.
 intro H.
 checkfail assumption exn NotHypothesis.
Abort.

lemma _ (x,y : message) : False => x = y <: Real.of_int 12.
Proof.
 intro H.
 assumption.
Qed.

lemma _ (x,y : message) : False => x = y <: Real.(-) (Real.of_int 12) (Real.of_int 13).
Proof.
 intro H.
 checkfail assumption exn NotHypothesis.
Abort.

lemma _ (i:index,t:timestamp) :
happens(t) => R(i) <> t <: Real.div (Real.of_int 1) (Real.of_int 2) .
Proof.
 checkfail (intro H; auto) exn GoalNotClosed.
Abort.
