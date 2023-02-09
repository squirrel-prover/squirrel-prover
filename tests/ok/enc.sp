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
  
  * expandall.
    by fresh 1.
  
  * expandall.
    fa 2; fa 3; fa 3; fa 3.  
    cca1 3. 
     + auto. 
     + fa 3.
       fresh 4; 1:auto.
       rewrite len_n in 3.
       auto.
Qed.
