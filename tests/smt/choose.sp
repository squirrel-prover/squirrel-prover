include Core.
set smtSteps=10000.

abstract ok : message. 
mutable s(i:index) : message = ok.
channel c.

process test = 
  let i = choose (fun i => s(i) = ok) in out(c,s(i)) 

system  test.

lemma _ : happens(test) => output@test = ok. Proof. smt. Qed.

lemma [any] _ (i0:index) :
  (choose (fun i => i = i0)) = i0.
Proof. smt ~prover:CVC5. Qed.
