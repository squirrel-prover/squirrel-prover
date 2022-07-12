

(* Test that it is possible to undo the second block of declarations. *)
channel c.
system in(c,x);out(c,x).

undo 1.

system in(c,x);out(c,<x,x>).
goal test :
  happens(A) => output@A = <input@A,input@A>.
Proof.
 auto.
Qed.
