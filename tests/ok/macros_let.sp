set autoIntro=false.

channel c
system
  in(c,x);
  let y = <x,x> in
  out(c,y).

goal _: output@A = <input@A,input@A>.
Proof.
 by auto.
Qed.
