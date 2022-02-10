set autoIntro=false.
set newInduction=true.

hash h
channel c

name k : index -> message

name ok : message
name ko : message

system
!_i (if False then out(c,diff(ok,ko)) else out(c,h(ok,k(i)))).

equiv simp.
Proof.
enrich seq(i:index ->h(ok,k(i))).

 dependent induction t => t Hind Hap. 
 case t => H.

 auto.

 destruct H as [i H].
 expandall. 
 fa 1.
 fa 2. 
 noif 2; 1: auto.
 by apply Hind.

 destruct H as [i H].
 expandall.
 fa 1.
 fa 2.
 equivalent cond@t, True.
 by expand cond. 
 fa 2.

 by apply Hind.
Qed.
