(* This file tests the tactics `typing`.
   This file check that initial states are well-typed in a protocol.
   We consider the case of an empty (well-typed) protocol with a mutable
   state added after its declaration.
   The initialisation of this state is not well-typed. *)

set securityTypes = true.

channel c
name h : message, High
name l : message, Low.

system sys = null.

(* Now, we declare a mutable that does not type *)
mutable s : message, Low = h. 

lemma[sys] _ : h = s@init => false.
Proof.
  intro H.
  checkfail typing H exn Failure.
Abort.
