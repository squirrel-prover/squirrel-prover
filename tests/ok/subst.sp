
set debugTactics=true.

channel ch

abstract a : index -> message
abstract b : index -> message

system null.

axiom bar (i : index): a(i) = b(i) => False.

goal foo : 
  (exists (i, i1, i2 : index), a(i1) = b(i2)) => False.
Proof.
 intro [i1 Hap].
 destruct Hap as [i2 [i3 Ha]].
 use bar with i3; 1: auto. 
 checkfail (auto) exn GoalNotClosed.
Abort.
