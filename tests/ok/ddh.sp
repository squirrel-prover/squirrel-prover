set autoIntro=false.

name a : index -> message
name b : index -> message
name k : index -> message

ddh g, (^) where group:message exposants:message.

channel c

system !_i ( out(c, diff((g^a(i))^b(i),g^k(i)))).


equiv ddh_goal.
Proof.
induction t.

auto.

expand frame; expand exec.

by ddh g, a, b, k.
Qed.
