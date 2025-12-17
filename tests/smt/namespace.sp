set smtSteps=10000.

channel c.
namespace T.
process test =  t1 : out(c,empty).
system t = test.

lemma [t] _ : true.
Proof. smt. Qed.
