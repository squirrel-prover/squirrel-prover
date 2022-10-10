

include Basic.

mutable s(i:index): message = empty
abstract f : message->message

system !_i s(i):=f(s(i)).

goal update (i:index):
  happens(A(i)) => s(i)@A(i) = f(s(i)@pred(A(i))).
Proof.
  intro H.
  rewrite /s.
  auto.
Qed.

goal not_update (i,j:index):
  happens(A(j)) => i<>j => s(i)@A(j) = s(i)@pred(A(j)).
Proof.
  intro Hhap Hneq.
  expand s(i)@A(j). 
  by rewrite if_false.
Qed.
