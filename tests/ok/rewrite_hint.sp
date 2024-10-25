channel c.

op p : message.
op q : message.

mutable s = empty.
system P = null.
system Q = null.

axiom fooP in [P] t : s@t = p.
hint rewrite fooP.
axiom fooQ in [Q] t : s@t = q.
hint rewrite fooQ.

lemma _ in [any] t : s@t = p.
Proof.
  simpl.
Abort.  

lemma _ in [P] t : s@t = p && s@t = q.
Proof.
  split; 1: auto. 
  checkfail auto exn GoalNotClosed.
  admit.
Qed.

lemma _ in [Q] t : s@t = p && s@t = q.
Proof.
  split; 2: auto. 
  checkfail auto exn GoalNotClosed.
  admit.
Qed.

lemma _ in [P/left, Q/left] t : s@t = diff(p,q) && s@t = diff(q,p).
Proof.
  split; 1: project; auto. 
  checkfail project; auto exn GoalNotClosed.
  admit.
Qed.

