

name a : index -> message
name b : index -> message
name k : index -> message

ddh g, (^) where group:message exponents:message.

channel c

system (!_i ( out(c, diff((g ^ a(i)) ^ b(i),g ^ k(i))))
       | !_j ( in(c,x);out(c,g ^ x ^ a(j)))
       ).


equiv ddh_goal.
Proof.
 nosimpl(induction t).
 fadup; expandall; refl + assumption.
 fadup; try (expandall; refl + assumption).
 fadup; try (expandall; refl + assumption).
 cycle 1.
 nosimpl(expandall).

 fadup; try (expandall; refl + assumption).

 fa 0; fa 1; fa 1.
 ddh g, a, b, k.
Qed.
