abstract ok : message
abstract ko : message
abstract koo : message

channel c

process A(res:message) =  in(c,x);out(c,x); B: in(c,y); if y=ok then out(c,res)

system A(diff(ok,ko)).

system [toto] A(diff(ko,koo)).


goal test : output@B = diff(ok,ko).
Proof.
  intros.
Qed.

goal [left] test_left : cond@B => output@B = input@B.
Proof.
expand cond@B.
Qed.

goal [right] test_right : output@B = ko.
Proof.
  intros.
Qed.

goal [none, toto] test2 : output@B = diff(ko,koo).
Proof.
  intros.
Qed.

goal [left, toto] test_left2 : cond@B => output@B = ko.
Proof.
expand cond@B.
Qed.

goal [right, toto] test_right2 : output@B = koo.
Proof.
  intros.
Qed.
