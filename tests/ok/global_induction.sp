(* check global induction over timestamps, as it automatically does a 
   case analysis: deterministic is necessary *)

channel c

system (in(c,x);out(c,x) | !_i in(c,x);out(c,x)).

global lemma _ (t:timestamp) :
  [t = init] \/ [t = A] \/ Exists (i:index), [t = A1(i)].
Proof. 
  checkfail induction t exn Failure. 
Abort.

global lemma _ (t:timestamp[const]) :
  [t = init] \/ [t = A] \/ Exists (i:index), [t = A1(i)].
Proof. 
  induction t. 
  + by left. 
  + by right; left. 
  + by right; right; exists i.
Qed.

(* dependent global induction does not automatically do a case analysis, 
   hence `det` is not necessary *)
global lemma _ (t:timestamp) :
  [t = init] \/ [t = A] \/ Exists (i:index), [t = A1(i)].
Proof. 
  dependent induction t.
Abort.
