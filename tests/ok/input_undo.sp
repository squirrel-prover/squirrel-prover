

(* Test that it is possible to undo the first system declaration. *)
channel c
system in(c,x);out(c,x).

undo 1.

channel c
system in(c,x);out(c,<x,x>).
lemma test :
  happens(A) => output@A = <input@A,input@A>.
Proof.
 auto.
Qed.
