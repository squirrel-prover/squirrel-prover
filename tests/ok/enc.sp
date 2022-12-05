include Basic.

channel c
name sk : message

name n : message
name m : message

name r : index -> message

aenc enc,dec,pk

system !_i out(c,<diff(n,m), enc(n,r(i),pk(sk))>).

abstract eta:message.
axiom len_n: len(n) = eta.

equiv test.
Proof.
  enrich diff(n,m).
  enrich pk(sk).
  
  induction t.
  
  expandall.
  fresh 1.
  auto.
  
  expandall.
  fa 2; fa 3; fa 3; fa 3.  
  cca1 3. 
   + auto. 
   + fa 3.
     fresh 4.  
     rewrite len_n in 3.
     rewrite if_true in 3; auto.
Qed.
