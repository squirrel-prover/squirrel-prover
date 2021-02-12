set autoIntro=false.

name n : message
name k : message
hash h
channel c

system in(c,x);out(c,h(x,k)).

goal foo :
  h(<n,input@A>,k) = n => False.
Proof.
  intro Heq.
  euf Heq. 
  by auto.
Qed.
