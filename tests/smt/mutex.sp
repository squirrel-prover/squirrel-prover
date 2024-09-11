abstract ok : message
abstract ko : message 
channel c

process A_real_test = 
  in(c,m);
  if m=ok then 
    out (c,ko) 
  else 
    out (c,ok)

system real = ( A : A_real_test).

lemma[real] _ : not(happens(A)) || not(happens(A1)).
Proof. smt. Qed.
   
