

(* This file contains an unsound axiom, dummy_false_axiom.
   It is a test of application of an axiom with existential variables *)

name k:message

system null.

axiom dummy_false_axiom (ma : message):
exists (m:message), m=k && ma=k.

lemma [default/left] dummy (ma : message) : ma=k.
Proof.
 by use dummy_false_axiom with ma. 
Qed.

lemma [default/right] _ (ma : message): ma=k.
Proof.
 by use dummy_false_axiom with ma.
Qed.

lemma _ (ma : message) : ma=k.
Proof.
 by use dummy_false_axiom with ma.
Qed.
