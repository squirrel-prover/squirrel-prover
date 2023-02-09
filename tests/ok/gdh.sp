channel c

type E [large].

gdh g, (^), ( ** ) where group:message exponents:E.

cdh gg, (^^) where group:message exponents:E.

abstract top : message.
abstract bot : message.

name a : index -> E.
name b : index -> E.
name d : index -> E.

abstract toM : E -> message.

abstract corrupted : index -> boolean.

abstract toMB : boolean -> message.

process init (i:index) =
  let ai = a(i) in
  let ga = g ^ ai in
  I: out(c, ga).

process resp (i:index) =
  let gb = g ^ b(i) in
  R: out(c, gb).

process badguy (i:index) =
  B: out(c, toM (d(i))).

process leak (i:index, j:index) =
  L: out(c, <g ^ (b(i) ** a(i)),
              (< toM(a(j)),
                 toMB (g^a(i)^(b(i)**b(j)) = toM(a(i)) ^ d(i) ^ b(j)) >) >).

process leak2 (i:index) =
  L2: out(c, g ^ d(i) ^ b(i)).

process DHoracle (i:index,j:index) =
  in(c, x);
  in(c, y);
  if x = g^a(i)^b(j) || g^d(i)^a(i) = y^a(i)
  || x = y^a(i)
  || y^b(j) = x
  || x^a(i) = y^a(j)
  || x^b(i) = y^b(j)
  || x^a(i) = y^b(j)
  || x^b(j) = g^a(i)^b(j)
  || y^a(i) = g^(a(i)**b(j))
  || y^b(i) = g^(a(i)**a(j))
  || y^a(i) = g^(a(i)**a(j))
  || y^a(i) = g^(b(i)**b(j))
  || y^b(i) = g^(b(i)**b(j))
  || y = g^(a(i)**a(j))
  || y = g^(b(i)**b(j))
then
    out(c, top)
  else
    out(c, bot).


process protocol = 
  !_i (init(i) | resp(i) | badguy(i) | leak2(i) | !_j (leak(i,j) | DHoracle(i,j))).


system [default] protocol.

axiom corruptleak (i,j:index) :
  happens(L(i,j)) => corrupted(i) = true.

axiom corruptleak2 (i,j:index) :
  happens(L(i,j)) => corrupted(j) = true.

goal [default/left] test_gdh (t:timestamp[glob,const]) (i,j : index[glob,const]) :
  corrupted(i) = false =>
  corrupted(j) = false =>
  happens(I(i), R(j)) =>
  att(frame@t) = g ^ a(i) ^ b(j) =>
  false.
Proof.
  intro HC HC2 Hhap H.
  gdh H, g ; intro HH; destruct HH as [j0 HH].
  use corruptleak with i, j0 as H';
    [1: by rewrite -HC H' | 2:by constraints].  
  use corruptleak2 with j0, i as H';
    [1:by rewrite -HC H' | 2: by constraints].  
  use corruptleak with j, j0 as H';
    [1:by rewrite -HC2 H' | 2: by constraints].  
Qed.



goal [default/left] test_cdh (t:timestamp) (i,j : index) :
  corrupted(i) = false =>
  happens(I(i), R(j)) =>
  att(frame@t) = g ^ a(i) ^ b(j) =>
  false.
Proof.
  intro HC Hhap H.
  rewrite -HC.
  checkfail (cdh H, g  ; intro HH; auto) exn GoalNotClosed.
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

axiom [system2] corruptleak3 (i:index) :
  happens(B(i)) => corrupted(i) = true.

process protocol3 = 
  !_i (init2(i) | resp2(i) | leak4(i)).


system [system3] protocol3.

axiom [system3] corruptleak4 (i:index) :
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
  by rewrite corruptleak3.
Qed.


goal [system3/left] test_cdh3 (t:timestamp) (i,j : index) :
  not(happens(B(i))) =>
  happens(I(i), R(j)) =>
  att(frame@t) = gg ^^ a(i) ^^ b(j) =>
  false.
Proof.
  intro HC Hhap H.
  checkfail (by cdh H, gg  ; intro HH) exn GoalNotClosed.
Abort.

