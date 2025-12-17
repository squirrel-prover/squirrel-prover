set smtSteps=100000.

abstract f : (bool -> bool) -> bool.
abstract a : message -> bool -> bool.
abstract g : bool -> bool.
abstract h : bool -> (bool -> bool).

lemma[any] _ : f g || not (f g). Proof. smt. Qed.

lemma[any] _ (x:message): (a x) = (a x). Proof. smt. Qed.

lemma[any] _ : forall f:bool->bool, f true || not (f true). Proof. smt. Qed.

lemma[any] _ : exists f:bool->bool, f(true)=true. Proof. smt ~prover:Z3_counterexamples. Qed. 

abstract ok : message. 

lemma[any] _ : exists f:message->bool, f(empty)=true. Proof. smt ~prover:Z3_counterexamples. Qed. 

lemma[any] _ : exists f:message->bool, f(ok)=true. Proof. smt ~prover:Z3. Qed. 

lemma[any] _ : forall x:bool, forall y:bool, h(x)(y) || not( h(x)(y)).
Proof. smt. Qed.

lemma[any] _ : forall x:bool, (fun x:bool => x||not(x)) x.
Proof. smt. Qed.

lemma[any] _['a] : forall f : 'a->bool, forall x:'a, f(x) || not(f(x)).
Proof. smt. Qed.
