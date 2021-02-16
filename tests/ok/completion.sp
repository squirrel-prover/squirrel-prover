set autoIntro=false.

abstract m1 : message
abstract m2 : message
abstract m3 : message

abstract h : message -> message

system null.

goal _:  False.
Proof.
assert fst( h(<<m3,m2>,m3>))=m1.
assert  <m1,m2> = h(<<m3,m2>,m3>).
admit.
admit.
Qed.

goal _ (x:message) : False.
Proof.
intro x.
assert fst( h(<<m3,x>,m3>))=m1.
assert  <m1,m2> = h(<<m3,x>,m3>).
admit.
admit.
Qed.

goal _ (x:message) : <m1,m2> <> h(<<m3,x>,m3>).
Proof.
intro x Heq.
assert fst( h(<<m3,x>,m3>))=m1.
admit.
Qed.
