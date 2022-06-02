

(* remove automatic FADup, for tests *)
set autoFADup=false.

system null.

name n : message.

name a : message.
name b : message.
name c : message.
name d : message.

abstract f : message -> message.
abstract g : message -> message -> message.

(*------------------------------------------------------------------*)
global goal _ : 
  (equiv(diff(a,b), diff(c,d))) ->
  equiv(f(diff(a,b)), f(diff(c,d))).
Proof. 
  intro H. 
  fa f (_).
  fa f (_).
  apply H.
Qed.

(*------------------------------------------------------------------*)
global goal _ : 
  equiv (a,b,diff(a,b)) ->
  equiv(f(a), g(f(a), f(b)), g(f(a), b), diff(a,b)).
Proof.
  intro H.
  fa f (_).
  fa g (_,_).
  fa g (_,_).
  fa f (_), f (_), f (_).
  apply H.
Qed.

(* same with more restrictive patterns *)
global goal _ : 
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
global goal _ : 
  equiv (a,b,diff(a,b)) ->
  equiv(f(a), g(f(a), f(b)), g(f(a), b), diff(a,b)).
Proof.
  intro H. 
  fa f (_), g (_,_), g (_,_), f (_), f (_), f (_).
  apply H.
Qed.

(* same with multiplicities *)
global goal _ : 
  equiv (a,b,diff(a,b)) ->
  equiv(f(a), g(f(a), f(b)), g(f(a), b), diff(a,b)).
Proof.
  intro H.
  fa !g (_,_), !f (_).
  apply H.
Qed.

global goal _ (t : timestamp): equiv(frame@t).
Proof.
  try fa frame@_.
Abort.
