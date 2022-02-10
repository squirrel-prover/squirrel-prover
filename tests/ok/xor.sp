set autoIntro=false.

name n1 : message

abstract ok : message
abstract ko : message

abstract f : message -> message

name dummy : message

system null.

axiom len_ok : len(ok) = len(dummy)
axiom len_ko : len(ko) = len(dummy).

goal _ (t:timestamp):
  xor(output@t,output@t) = zero.
Proof.
 auto.
Qed.

goal _ (m:message,t:timestamp):
  xor(output@t,xor(m,output@t)) = m.
Proof.
 auto.
Qed.

goal _ (m:message,n:message,x:message):
  x = xor(m,<m,n>) &&
  snd(xor(x,m)) = m =>
  m = n.
Proof.
 auto.
Qed.

equiv test : diff(xor(n1,ok),xor(n1,ko)).
Proof.
  xor 0.
  yesif 0.
  by use len_ok; use len_ko; namelength n1,dummy.
  auto.
Qed.


equiv testf : diff(f(xor(n1,ok)),f(xor(n1,ko))).
Proof.
  xor 0, n1.
  yesif 0.
  by use len_ko;  namelength n1,dummy.
  xor 0, xor(n1,ok), n1.
  yesif 0.
  by use len_ok;  namelength n1,dummy.
  fa 0.
  fresh 0.
  auto.
Qed.
