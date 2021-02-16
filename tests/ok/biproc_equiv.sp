set autoIntro=false.

channel c
system A: in(c,x);out(c,zero);
       B: in(c,y); if False then out(c,diff(x,y)) else out(c,zero).



goal trivial_if : happens(B) => cond@B => False.
Proof.
intro Hap Hcond.
expand cond@B.
Qed.

equiv test_left_bis.
Proof.
induction t.

expand frame@A.
by fa 0.

expand frame@B.
fa 0; fa 1.
expand exec@B.
equivalent cond@B, False. 
by intro Hcond; apply trivial_if.
noif 1.
by auto.
expand frame@B1.
by fa 0.
Qed.
