

channel c
abstract ok:message

system in(c,x); if x=ok && x<>ok then out(c,x).

equiv test.
Proof.
induction t.

auto.

expand frame@A.
expand exec@A.
have -> : cond@A <=> False.
by expand cond@A. 
by fa 0.

expand frame@A1.
expand exec@A1.
have -> : cond@A1 <=> True.
by expand cond@A1.

by fa 0.
Qed.
