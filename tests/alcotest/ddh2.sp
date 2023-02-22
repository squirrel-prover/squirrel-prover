name a : index -> message
name b : index -> message
name k : index -> message

channel c

ddh g, (^)

system (!_i ( out(c, diff((g^a(i))^b(i),g^k(i))))
       | !_j ( in(c,x);out(c,diff(g^k(j),g^k(j))))
       )
.


equiv ddh_goal.
Proof.
induction t.
auto.
expand frame@A(i);
expand exec@A(i);
expand cond@A(i);
expand output@A(i).
fa 0. fa 1. fa 1.
ddh g, a, b, k.

expandall.
fa 0;fa 1;fa 1.
ddh g, a, b, k.
Qed.
