

type E[large].

name a : index -> E
name b : index -> E
name k : index -> E

ddh g, (^) where group:message exponents:E.

channel c

system !_i ( out(c, diff(g^a(i)^b(i),g^k(i)))).


equiv ddh_goal.
Proof.
induction t.

auto.

expand frame; expand exec.

by ddh g, a, b, k.
Qed.
