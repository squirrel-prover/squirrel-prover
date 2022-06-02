

name a : index -> message
name b : index -> message
name k : index -> message

channel c

system (!_i ( out(c, diff((g^a(i))^b(i),g^k(i))))
       | !_j ( in(c,x);out(c,diff(g^k(j),g^k(j))))
       )
.


equiv ddh_goal.
Proof.
induction t.

expand frame@A(i); expand exec@A(i); expand cond@A(i); expand output@A(i).

fa 0. fa 1. fa 1.

ddh a,b,k.
Qed.
