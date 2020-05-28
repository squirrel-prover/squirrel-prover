channel c
system A: in(c,x);out(c,zero);
       B: in(c,y); if False then out(c,diff(x,y)) else out(c,zero).



goal trivial_if : cond@B => False.
Proof.
simpl.
expand cond@B.
Qed.

equiv test_left_bis.
Proof.
induction t.

expand frame@A.
fa 0.

expand frame@B.
fa 0. fa 1.
expand exec@B.
equivalent cond@B, False.
apply trivial_if.
noif 1.

expand frame@B1.
fa 0.

Qed.
