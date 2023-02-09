include Basic.

hash h

name key : message
name seed : message

mutable kT : message = seed

channel c

process tag(j:index) =
  T: out(c, h(kT,key)).

system !_j tag(j).

axiom no_repeat (i, j:timestamp): i < j => kT@j <> kT@i.

global goal foo (t: timestamp[param]) :
  [forall (j, j0:index), (T(j0) < T(j) => kT@pred(T(j)) <> kT@T(j0))] ->
  [happens(t)] ->
  equiv(frame@t).
Proof.
  intro H.
  induction t.
  
  (* t = init *)
  by intro *.
  
  (* t = T(j) *)
  intro H1.
  expand frame, exec, output, cond, kT. 
  
  fa 0.
  fa 1.
  fa 1.
  prf 1.
  simpl. 
  rewrite if_true in 1. 
  by intro > _ @/kT; apply H. 
  fresh 1; 1:auto.
  by apply IH. 
Qed.
