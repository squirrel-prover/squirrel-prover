

hash h
name k:message
channel c
channel c2
name n:index -> message
name m:index -> message
system null.

abstract ok : message.


system [test] (!_i A: out(c, diff(n(i),m(i)) ) | (!_i B: out(c, diff(n(i),m(i)) ) )).

system newTest = [test/left] with rename Forall (i:index), equiv(diff(n(i),m(i))).

equiv [newTest,test/right] tutu.
Proof.
help.
print.
diffeq.
Qed.

(* TODO: clean transitivity for the full equiv proof of test *)
