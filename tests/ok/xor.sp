set autoIntro=false.

name n1 : message

abstract ok : message
abstract ko : message

name dummy : message

system null.

axiom len_ok : len(ok) = len(dummy)
axiom len_ko : len(ko) = len(dummy).

goal forall (t:timestamp),
  xor(output@t,output@t) = zero.
Proof.
 by auto.
Qed.

goal forall (m:message,t:timestamp),
  xor(output@t,xor(m,output@t)) = m.
Proof.
 by auto.
Qed.

goal forall (m:message,n:message,x:message),
  x = xor(m,<m,n>) &&
  snd(xor(x,m)) = m =>
  m = n.
Proof.
 by auto.
Qed.

equiv test : diff(xor(n1,ok),xor(n1,ko)).
Proof.
  xor 0.
  yesif 0.
  apply len_ok; apply len_ko; namelength n1,dummy. 
  by auto.
Qed.
