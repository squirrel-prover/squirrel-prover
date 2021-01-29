abstract ok : message
abstract ko : message
abstract koo : message

channel c

process A(res:message) =  in(c,x);out(c,x); B: in(c,y); if y=ok then out(c,res)

system A(diff(ok,ko)).

system [toto] A(diff(ko,koo)).


goal test : output@B = diff(ok,ko).
Proof.
  intro *.
Qed.

goal [left] test_left : cond@B => output@B = input@B.
Proof.
  intro Hc.
  expand cond@B.
Qed.

goal [right] test_right : output@B = ko.
Proof.
  intro *.
Qed.

goal [none, toto] test2 : output@B = diff(ko,koo).
Proof.
  intro *.
Qed.

goal [left, toto] test_left2 : cond@B => output@B = ko.
Proof.
  intro *.
Qed.

goal [right, toto] test_right2 : output@B = koo.
Proof.
  intro *.
Qed.
