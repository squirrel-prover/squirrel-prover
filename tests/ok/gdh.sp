set autoIntro = false.

channel c

gdh g, (^), ( ** ) where group:message exponents:message.

cdh gg, (^^) where group:message exponents:message.

abstract top : message.
abstract bot : message.

name a : index -> message.
name b : index -> message.
name d : index -> message.

abstract corrupted : index -> boolean.

process init (i:index) =
  let ai = a(i) in
  let ga = g ^ ai in
  I: out(c, ga).

process resp (i:index) =
  let gb = g ^ b(i) in
  R: out(c, gb).

process badguy (i:index) =
  B: out(c, d(i)).

process leak (i:index) =
  L: out(c, g ^ (b(i) ** a(i))).

process leak2 (i:index) =
  L2: out(c, g ^ d(i) ^ b(i)).

process DHoracle (i:index) =
  in(c, x);
  if x = g^a(i)^b(i) then
    out(c, top)
  else
    out(c, bot).

process protocol = 
  !_i (init(i) | resp(i) | badguy(i) | leak(i) | leak2(i) | DHoracle(i)).


system [default] protocol.

axiom corruptleak (i:index) :
  happens(L(i)) => corrupted(i) = true.

goal [default/left] test_gdh (t:timestamp) (i,j : index) :
  corrupted(i) = false =>
  happens(I(i), R(j)) =>
  att(frame@t) = g ^ a(i) ^ b(j) =>
  false.
Proof.
  intro HC Hhap H.
  rewrite -HC.
  gdh H, g ; intro HH; by rewrite corruptleak.
Qed.  

goal [default/left] test_cdh (t:timestamp) (i,j : index) :
  corrupted(i) = false =>
  happens(I(i), R(j)) =>
  att(frame@t) = g ^ a(i) ^ b(j) =>
  false.
Proof.
  intro HC Hhap H.
  rewrite -HC.
  checkfail (cdh H, g  ; intro HH; by rewrite corruptleak) exn GoalNotClosed.
Abort.


goal [default/left] test_gdh2 (t:timestamp) (i,j : index) :
  att(frame@t) = gg ^^ a(i) ^^ b(j) =>
  false.
Proof.
  intro H.
  checkfail (gdh H, gg) exn Failure.
  checkfail (by cdh H, gg) exn GoalNotClosed.
Abort.




process init2 (i:index) =
  let ai = a(i) in
  let ga = gg ^^ ai in
  out(c, ga).

process resp2 (i:index) =
  let gb = gg ^^ b(i) in
  out(c, gb).

process leak3 (i:index) =
  out(c, gg ^^ b(i) ^^ a(i)).

process leak4 (i:index) =
  out(c, gg ^^ (b(i) ** a(i))).


process protocol2 = 
  !_i (init2(i) | resp2(i) | leak3(i)).


system [system2] protocol2.

axiom [system2] corruptleak2 (i:index) :
  happens(B(i)) => corrupted(i) = true.

process protocol3 = 
  !_i (init2(i) | resp2(i) | leak4(i)).


system [system3] protocol3.

axiom [system3] corruptleak3 (i:index) :
  happens(B(i)) => corrupted(i) = true.

goal [system2/left] test_cdh2 (t:timestamp) (i,j : index) :
  corrupted(i) = false =>
  happens(I(i), R(j)) =>
  att(frame@t) = gg ^^ a(i) ^^ b(j) =>
  false.
Proof.
  intro HC Hhap H.
  rewrite -HC.
  checkfail (gdh H,gg) exn Failure.
  cdh H, gg; intro HH.
  destruct HH as [i0 [HH HHH]].      
  by rewrite corruptleak2.
Qed.


goal [system3/left] test_cdh3 (t:timestamp) (i,j : index) :
  not(happens(B(i))) =>
  happens(I(i), R(j)) =>
  att(frame@t) = gg ^^ a(i) ^^ b(j) =>
  false.
Proof.
  intro HC Hhap H.
  checkfail (by cdh H, gg  ; intro HH; destruct HH as [i0 [HH HHH]]) exn GoalNotClosed.
Abort.

