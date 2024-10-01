
include Basic.
channel c
name sk : message

name n : message
name m : message

name r : index -> message

senc enc,dec

system !_i out(c,<diff(n,m), enc(n,r(i),sk)>).

abstract eta:message.
axiom [default] len_n: len(n) = eta.


equiv test.
Proof.
enrich diff(n,m).

induction t.

expandall.
by fresh 0.

expandall.
fa 1; fa 2; fa 2; fa 2.  cca1 2.
  + auto.
  + rewrite len_n in 2.
    fa 2.
    fresh 2; [1: auto].
    checkfail auto exn GoalNotClosed.
Abort.


name r2 : index -> message.

system s2 = !_i out(c,<enc(n, r(i), sk), <enc(n,r2(i),sk), enc(<m,n>, r2(i), sk)>>).

equiv [s2] test2.
Proof.
enrich diff(n,m).

induction t.

expandall.
by fresh 0.

expandall.
fa 1; fa 2; fa 2; fa 2.  cca1 2.
  + checkfail auto exn GoalNotClosed.
Abort.
