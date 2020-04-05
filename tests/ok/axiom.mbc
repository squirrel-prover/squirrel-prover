(* This file contains an unsound axiom, dummy_false_axiom.
   It is a test of application of an axiom with existential variables *)

name k:message


axiom dummy_false_axiom :
forall (ma : message),
exists (m:message), m=k && ma=k


system  null.

goal [left] dummy :
forall (ma : message),
ma=k.

Proof.
 simpl.
 apply dummy_false_axiom to ma.
Qed.

goal [right]
forall (ma : message),
ma=k.

Proof.
 simpl.
 apply dummy_false_axiom to ma.
Qed.

goal
forall (ma : message),
ma=k.

Proof.
 simpl.
 apply dummy_false_axiom to ma.
Qed.
