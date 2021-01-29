(* Test that it is possible to undo the first system declaration. *)
channel c
system in(c,x);out(c,x).
undo 1.
channel c
system in(c,x);out(c,<x,x>).
goal test :
  output@A = <input@A,input@A>.
Proof.
 by auto.
Qed.
