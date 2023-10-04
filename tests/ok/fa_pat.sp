(* remove automatic FADup, for tests *)
set autoFADup=false.

system null.

name n : message.

name a : message.
name b : message.
name c : message.
name d : message.

abstract f : message -> message.


(*------------------------------------------------------------------*)
global lemma _ : 
  (equiv(diff(a,b), diff(c,d))) ->
  equiv(f(diff(a,b)), f(diff(c,d))).
Proof. 
  intro H. 
  fa f (_).
  fa f (_).
  apply H.
Qed.

(*==================================================================*)
abstract g0 : message -> message -> message.

(*------------------------------------------------------------------*)
global lemma _ : 
  equiv (a,b,diff(a,b)) ->
  equiv(f(a), g0 (f a) (f b), g0 (f a) b, diff(a,b)).
Proof.
  intro H.
  fa f _.
  fa g0 _ _.
  fa g0 _ _.
  fa f _, f _, f _.
  apply H.
Qed.

(* same with more restrictive patterns *)
global lemma _ : 
  equiv (a,b,diff(a,b)) ->
  equiv(f(a), g0 (f a) (f b), g0 (f a) b, diff(a,b)).
Proof.
  intro H.
  fa f _.
  fa g0 _ b.
  fa f _.  
  fa g0 (f _) _.
  fa f _, f _.
  apply H.
Qed.

(*==================================================================*)
(* again, using a function `g` taking a tuple as input *)

abstract g : message * message -> message.

(*------------------------------------------------------------------*)
global lemma _ : 
  equiv (a,b,diff(a,b)) ->
  equiv(f(a), g(f(a), f(b)), g(f(a), b), diff(a,b)).
Proof.
  intro H.
  fa f (_).
  fa g (_,_).
  fa g (_,_). 
  fa f _, f (_), f (_).
  apply H.
Qed.

(* same with more restrictive patterns *)
global lemma _ : 
  equiv (a,b,diff(a,b)) ->
  equiv(f(a), g(f(a), f(b)), g(f(a), b), diff(a,b)).
Proof.
  intro H.
  fa f (_).
  fa g (_,b).
  fa f (_).  
  fa g (f (_),_).
  fa f (_), f (_).
  apply H.
Qed.

(* same but chaining FAs *)
global lemma _ : 
  equiv (a,b,diff(a,b)) ->
  equiv(f(a), g(f(a), f(b)), g(f(a), b), diff(a,b)).
Proof.
  intro H. 
  fa f (_), g (_,_), g (_,_), f (_), f (_), f (_).
  apply H.
Qed.

(* same with multiplicities *)
global lemma _ : 
  equiv (a,b,diff(a,b)) ->
  equiv(f(a), g(f(a), f(b)), g(f(a), b), diff(a,b)).
Proof.
  intro H.
  fa !g (_,_), !f (_).
  apply H.
Qed.

global lemma _ (t : timestamp): equiv(frame@t).
Proof.
  try fa frame@_.
Abort.

(*------------------------------------------------------------------*)
global lemma _ : 
  equiv(  diff(a,b), diff(c,d)  ) ->
  equiv( (diff(a,b), diff(c,d)) ).
Proof.
  intro H.
  fa (_,_).
  assumption H.
Qed.

global lemma _ : 
  equiv(  diff(a,b), diff(c,d)  ) ->
  equiv( (diff(a,b), diff(c,d)), (diff(a,b), diff(c,d))  ).
Proof.
  intro H.
  fa 2!(_,_).
  assumption H.
Qed.
