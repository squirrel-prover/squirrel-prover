set autoIntro=false.

hash h
name k : message
abstract ok : message
channel c

system !_i in(c,x); if fst(x)=h(snd(x),k) then out(c,h(ok,k)).

(* This axiom is incorrect, due to the special minimal element
 * in timestamp domains of meta-interpretations, but we cannot
 * write it with A(i) instead of t because A is not yet
 * created. TODO *)
axiom happens_le :
  forall (t:timestamp,tt:timestamp),
  t <= tt && happens(tt) => happens(t).

goal
  forall (t:timestamp,i:index),
  t = A(i) => not(happens(t)).
Proof.
  induction.
  intro Hind i Heq Hhap.
  assert(happens(A(i))).
  by apply happens_le to A(i), t.
  euf C.
  intro Hle Eqin.
  apply happens_le to A(i1), A(i).
  apply Hind to A(i1), i1.
Qed.
