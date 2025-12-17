set smtSteps=10000.

name s0 : index -> message.
mutable cellR(i:index) : message = s0 i.
hash H.
name key : message.
channel c.
abstract ok:message.

system a = null.

lemma [a] state_macros_init: forall(i', i'':index), 
s0(i') = s0(i'').
Proof.
intro *.
checkfail (smt ~prover:Z3) exn Failure.
Abort.

process A(i:index) = cellR(i):=H(cellR(i),key); out(c,ok).
process B(i:index) = out(c,ok).
system b = !_i (A(i)|B(i)).

lemma [b] state_macro_update: 
 forall(i:index,t:timestamp), cellR(i)@t = cellR(i)@pred(t).
Proof. 
  checkfail smt exn Failure.
Abort.
