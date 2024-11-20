channel c.

op p : message.
op q : message.

mutable s = empty.
system P = null.
system Q = null.

axiom fooP @system:P t : s@t = p.
hint rewrite fooP.
axiom fooQ @system:Q t : s@t = q.
hint rewrite fooQ.

lemma _ @system:any t : s@t = p.
Proof.
  simpl.
Abort.  

lemma _ @system:P t : s@t = p && s@t = q.
Proof.
  split; 1: auto. 
  checkfail auto exn GoalNotClosed.
  admit.
Qed.

lemma _ @system:Q t : s@t = p && s@t = q.
Proof.
  split; 2: auto. 
  checkfail auto exn GoalNotClosed.
  admit.
Qed.

lemma _ @system:(P/left, Q/left) t : s@t = diff(p,q) && s@t = diff(q,p).
Proof.
  split; 1: project; auto. 
  checkfail project; auto exn GoalNotClosed.
  admit.
Qed.

