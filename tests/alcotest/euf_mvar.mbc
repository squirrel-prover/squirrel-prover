(** This test should fail, euf should not apply when message variables
  * are present. Specifically, the syntactic side condition should fail.
  *)

hash h
name k:message
name cst:message

channel c

name n : message


system null.


goal cheat :
  forall (m1: message, m2:message, m3:message),
  h(m3,k) = m1 => m3 <> m2  .
Proof.
  simpl.
  euf M0.
Qed.
