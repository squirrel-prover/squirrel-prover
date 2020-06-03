channel c
system
  in(c,x);
  let y = <x,x> in
  out(c,y).

goal output@A = <input@A,input@A>.
Proof.
 simpl.
Qed.
