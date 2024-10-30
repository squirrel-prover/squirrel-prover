system toto = null.

(* No projection. *)

global axiom [set:toto/left, toto/left; equiv:toto/left,toto/left] foo :
  [false].

global lemma [set:toto/left, toto/left; equiv:toto/left,toto/left] _ : [false].
Proof.
  apply foo.
Qed.

(* Expansion from left to left,left. *)

global axiom [set:toto/left; equiv:toto/left,toto/left] bar :
  [false].

global lemma [set:toto/left, toto/left; equiv:toto/left,toto/left] _ : [false].
Proof.
  apply bar.
Qed.

(* Project and expand. This used to be "supported" by accident but
   without properly projecting. *)

global axiom [set:toto/left, toto/right; equiv:toto/left,toto/left] baz :
  [diff(false,true)].

global lemma [set:toto/left, toto/left; equiv:toto/left,toto/left] _ : [false].
Proof.
  have _ := baz.
  (* diff(false,true) should have been projected to false *)
  auto.
Qed.
