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
expand frame@init; expand exec@init.

ddh g, a, b, k.
Qed.
