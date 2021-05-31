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

 dependent induction t => t Hind Hap. 
 case t => H.

 auto.

 destruct H as [i H].
 expandall. 
 fa 1.
 fa 2. 
 noif 2; 1: auto.
 apply Hind; 1,2: by byequiv. 

 destruct H as [i H].
 expand frame, output, exec.
 fa 1.
 fa 2.
 equivalent cond@t, True.
 by expand cond. 
 fa 2.

 apply Hind; 1,2: by byequiv.
Qed.
