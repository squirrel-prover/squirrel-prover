name n : message
name k : message
hash h
channel c

system in(c,x);out(c,h(x,k)).

goal foo :
  happens(A) => h(<n,input@A>,k) = n => False.
Proof.
  intro Hap Heq.
  euf Heq. 
  auto.
Qed.
