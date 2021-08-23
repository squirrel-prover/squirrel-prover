set autoIntro=false.

abstract ok : index->message
channel c

(*------------------------------------------------------------------*)
system A: !_i in(c,x);out(c,<ok(i),x>).

axiom if_true (x,y : message): if true then x else y = x.

axiom if_false  (x,y : message): if false then x else y = y.

(*------------------------------------------------------------------*)
global goal _ (x : message): 
  equiv(x) -> [forall (i : index), ok(i) = x] ->
  equiv(seq(i:index -> diff(ok(i), x))).
Proof.
  intro Hx H.
  constseq 0: x. 
  by project. 
  assumption.
Qed.  

abstract ko : index->message.

(* sequence over a timestamp *)
global goal _ (x : message, t:timestamp, i:index): 
  equiv(x) -> [forall (i : index), ok(i) = ko(i)] ->
  equiv(seq(t':timestamp -> if t' < t then diff(ok(i), ko(i)))).
Proof.
  intro Hequiv Hi.
  constseq 0: (ok(i)) zero. 
  intro t'. 
  rewrite Hi.
  case (t' < t) => _. 
  by left; yesif; project. 
  by right; noif; project. 
  auto.
Qed.  

(*------------------------------------------------------------------*)
abstract even : index -> boolean.

global goal _ (x,y : message):
  equiv(x,y) -> 
  [forall (i : index), even(i) => ok(i) = x] ->
  [forall (i : index), not (even(i)) => ok(i) = y] ->
  equiv(seq (i:index -> diff(ok(i), if even(i) then x else y))).
Proof.
  intro Hx HE HO.
  constseq 0: x y; 2: assumption.
  intro i.
  project.
  case (even (i)) => He. 
  by left; apply HE.
  by right; apply HO.

  case even(i). 
  by rewrite if_true. 
  by rewrite !if_false.
Qed.  
