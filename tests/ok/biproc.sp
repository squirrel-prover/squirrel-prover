set autoIntro=false.

abstract ok : message
abstract ko : message
abstract koo : message

channel c

process A(res:message) =  in(c,x);out(c,x); B: in(c,y); if y=ok then out(c,res)

system A(diff(ok,ko)).

system [toto] A(diff(ko,koo)).


goal test : happens(B) => output@B = diff(ok,ko).
Proof.
  auto.
Qed.

goal [left] test_left : happens(B) => cond@B => output@B = input@B.
Proof.
  intro Hap Hc.
  expand cond@B.
Qed.

goal [right] test_right : happens(B) => output@B = ko.
Proof.
  auto.
Qed.

goal [none, toto] test2 : happens(B) => output@B = diff(ko,koo).
Proof.
  auto.
Qed.

goal [left, toto] test_left2 : happens(B) => cond@B => output@B = ko.
Proof.
  auto.
Qed.

goal [right, toto] test_right2 : happens(B) => output@B = koo.
Proof.
  auto.
Qed.
