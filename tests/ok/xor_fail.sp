name n1 : message.

abstract ok : message.
abstract ko : message.

channel c.

system out(c,<n1,diff(xor n1 ok, xor n1 ko)>).

include Basic.

equiv test.
Proof.
  induction t; try auto.
  expandall.
  fa 0.
  fa 1.
  fa 1.
  fa 1. 
  xor 2.
  rewrite ?if_false //=.
  checkfail auto exn GoalNotClosed.
  admit.
Qed.
