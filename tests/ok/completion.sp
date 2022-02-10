set autoIntro=false.

abstract m1 : message
abstract m2 : message
abstract m3 : message

abstract h : message -> message

system null.

goal _: <m1,m2> = h(<<m3,m2>,m3>) => fst( h(<<m3,m2>,m3>))=m1.
Proof. 
 auto. 
Qed.

goal _ (x:message) : <m1,m2> = h(<<m3,x>,m3>) => fst( h(<<m3,x>,m3>))=m1.
Proof. 
 auto. 
Qed.

goal _ (x:message) : <m1,m2> <> h(<<m3,x>,m3>).
Proof.
intro Heq.
assert fst( h(<<m3,x>,m3>))=m1. auto.
admit.
Qed.
