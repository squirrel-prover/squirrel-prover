(* This file tests the tactics `typing`.
   This file defines global and general macros.
   These macros are out of the scope of `typing`.
   However, global macros are automatically unfolded in a system. *)

set securityTypes = true.

channel c.

name h : message, High
name l : message, Low.

let m = h.

system sys1 = (in(c, x); let y = empty in out(c,y)).
system sys2 = (in(c, x); out(c,m)).

(* The tactic typing must succes with global macros, but not succeed with general macros.*)

lemma[sys1] _ : h=l => false.
Proof.
  intro H.
  typing H.
Qed.
lemma[sys2] _ : h=l => false.
Proof.
  intro H.
  checkfail typing H exn Failure.
Abort.
