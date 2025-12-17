set smtSteps=10000.

lemma _ @system:any (x:int) (y:message) : (x,y)#1 = x.
Proof.
  smt.
Qed.

lemma[any] _ : forall m:message, forall n:message, (m,n)#1=(n,m)#2.
Proof. smt. Qed.

lemma[any] _ (m:message*message,a:message) : m=(a,a) => m#1 = m#2.
Proof. smt. Qed.
