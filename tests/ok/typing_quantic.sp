(* This file tests the tactics `typing`.
   This file use quantic macros.
   These macros are out of the scope of `typing`, so we check
   they do not type. *)

set securityTypes = true.

channel c.

system [postquantum] sys = (in(c, x); out(c,x)).

(* The tactic typing must not succeed with quantic macros.*)

name h : message, High
name l : message, Low.

lemma[sys] _ : h=l => false.
Proof.
  intro H. 
  checkfail typing H exn Failure.
Abort.
