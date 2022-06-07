

channel c
system in(c,x);in(c,x);out(c,x).

goal testA :
  happens(A) => output@A = empty.
Proof. 
 auto.
Qed.

goal testA1 :
  happens(A1) => output@A1 = input@A1.
Proof.
 auto.
Qed.

system [bis] in(c,x);let y = <x,x> in in(c,x);out(c,<y,x>).

goal [bis] testAb :
  happens(A) => output@A = empty.
Proof. 
 auto.
Qed.

goal [bis] testA1b :
  happens(A1) => output@A1 = <<input@A, input@A>, input@A1>.
Proof.
 auto.
Qed.
