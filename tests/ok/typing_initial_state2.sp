(* This file tests the tactics `typing`.
   This file check that initial states are well-typed in a protocol.
   We consider here a protocol using a mutable with an initialisation
   that does not type accordingly to its declared type. *)

set securityTypes = true.

channel c
name h : message, High
name l : message, Low
mutable s : message, Low = h.

system sys = (in(c, x); out(c,s)).

lemma[sys] _ : h=l => false.
Proof.
  intro H.
  checkfail typing H exn Failure.
Abort.
