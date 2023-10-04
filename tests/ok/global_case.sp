(* check global case over timestamps: constant+si is necessary *)

channel c

system (in(c,x);out(c,x) | !_i in(c,x);out(c,x)).

global lemma _ (t:timestamp) :
  [t = init] \/ [t = A] \/ Exists (i:index), [t = A1(i)].
Proof. 
  checkfail case t exn Failure. (* [t] not deterministic *)
Abort.

global lemma _ (t:timestamp[const]) :
  [t = init] \/ [t = A] \/ Exists (i:index), [t = A1(i)].
Proof. 
  case t => ?.
  + by left. 
  + by right; left. 
  + right; right. 
    destruct H as [i _]. 
    by exists i.
Qed.
