set smtSteps=10000.

channel c.

abstract ok : message.
abstract ko : message.

system a = (A: out(c,diff(ok,ko))).

axiom [a] outA :  happens A => output@A=diff(ok,ko).

hint smt outA.

lemma [a/left] _ : happens A => output@A= ok.
Proof.
 smt ~no_macros.
Qed.

lemma [a/right] _ : happens A => output@A=ko.
Proof.
 smt ~no_macros.
Qed.
