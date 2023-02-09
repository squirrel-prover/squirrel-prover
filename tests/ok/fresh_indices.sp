name n : index -> message
name m : index -> message

abstract f : message -> index.

channel c

system !_i out(c,<n(i),seq(i:index => n(i))>).

include Basic.

(* indices of the name itself must be checked *)
global goal _ (i:index, j:index[const]) :
  equiv(diff(n(f(n(i))),m(i))).
Proof.
  checkfail fresh 0 exn Failure. (* non-deterministic variable *)
Abort.
