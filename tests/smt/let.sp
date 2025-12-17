set smtSteps=10000.

lemma[any] _ : let x = true in x.
Proof. smt. Qed. 

lemma[any] _ : let x = false in x.
Proof. checkfail smt exn Failure. Abort.

name n : index -> message.

lemma[any] _ (i,j:index) : let m = n(j) in n(i) = m => i=j.
Proof. smt. Qed.

include Core. 
open Classic. 

lemma[any] _ (phi:bool->bool) : phi(true) => let i = choose(phi) in phi(i).
Proof. smt. Qed.

channel c.
abstract ok: message.
abstract ko:message.

process A = let k = ok in
            A1: out(c,ok);
            A2: out(c,ok).

system [classic] P = A.

lemma [P] _: happens(A2) => k@A1 = k@A2.
Proof. 
smt.
Qed.


process B = let k = (exists (i:index), true ) in
            A1: out(c,ok);
            A2: out(c,ok).

system [classic] Q = B.

lemma [Q] _: happens(A2) => k@A1 = k@A2.
Proof. 
smt.
Qed.


process C = let k = try find (i:index) such that true in ok else ko in
            A1: out(c,ok);
            A2: out(c,ok).

system [classic] S = C.

lemma [S] _: happens(A2) => k@A1 = k@A2.
Proof. 
smt.
Qed.
