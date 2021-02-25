set autoIntro=false.

hash h
channel c

name k : index -> message

name ok : message
name ko : message

system
!_i (if False then out(c,diff(ok,ko)) else out(c,h(ok,k(i)))).

equiv simp.
Proof.
enrich seq(i->h(ok,k(i))).

 induction t. 
 expand frame@A(i).
 expand output@A(i).
 expand exec@A(i).
 fa 1.
 fa 2.
 equivalent cond@A(i), False.
 by expand cond@A(i); auto.
 noif 2. 
 by auto.

 expand frame@A1(i).
 expand output@A1(i).
 expand exec@A1(i).
 fa 1.
 fa 2.
 equivalent cond@A1(i), True.
 expand cond@A1(i). 
 by auto.
 fa 2.

 expand seq(i->h(ok,k(i))),i.
Qed.
