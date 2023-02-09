(* check global case over timestamps: deterministic is necessary *)

channel c

system (in(c,x);out(c,x) | !_i in(c,x);out(c,x)).

global goal _ (t:timestamp) :
  [t = init] \/ [t = A] \/ Exists (i:index), [t = A1(i)].
Proof. 
  checkfail case t exn Failure. (* [t] not deterministic *)
Abort.

global goal _ (t:timestamp[const]) :
  [t = init] \/ [t = A] \/ Exists (i:index), [t = A1(i)].
Proof. 
  case t => ?.
  + by left. 
  + by right; left. 
  + by right; right. 
Qed.
