set autoIntro=false.

(* This file contains an unsound axiom, dummy_false_axiom.
   It is a test of application of an axiom with existential variables *)

name k:message

system  null.

axiom dummy_false_axiom :
forall (ma : message),
exists (m:message), m=k && ma=k.

goal [left] dummy (ma : message) :
ma=k.

Proof.
 intro ma.
 apply dummy_false_axiom to ma. 
 auto.
Qed.

goal [right] _ (ma : message):
ma=k.

Proof.
 intro ma.
 apply dummy_false_axiom to ma.
 auto.
Qed.

goal _ (ma : message) :
ma=k.

Proof.
 intro ma.
 apply dummy_false_axiom to ma.
 auto.
Qed.
