

include Basic.

channel c
system A: in(c,x);out(c,zero);
       B: in(c,y); if False then out(c,diff(x,y)) else out(c,zero).



goal trivial_if : happens(B) => cond@B => False.
Proof.
intro Hap Hcond.
by expand cond@B.
Qed.

equiv test_left_bis.
Proof.
induction t.

auto.

expand frame@A.
by fa 0.

expand frame@B.
fa 0; fa 1.
expand exec@B.
assert -> : cond@B = False.
by expand cond@B. 
by rewrite if_false in 1.

expand frame@B1.
by fa 0.
Qed.
