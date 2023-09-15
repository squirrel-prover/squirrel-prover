include Basic.

channel c
name n : index -> message
name m : index -> message

process A (i:index) =
  out(c, diff(n(i), m(i))).

process B (i:index) =
  in(c, x).

system [S] (!_i A(i) | !_j B(j)). 


lemma [S/right, S/left] test (i,j:index) :
  n(i) <> input@B(j).
Proof.
intro H.
checkfail by fresh H exn GoalNotClosed.
Abort.

lemma [S/left] test (i,j:index) :
  n(i) <> input@B(j).
Proof.
intro H.
checkfail by fresh H exn GoalNotClosed.
Abort.

lemma [S/right] test (i,j:index) :
  n(i) <> input@B(j).
Proof.
intro H.
by fresh H.
Qed.
