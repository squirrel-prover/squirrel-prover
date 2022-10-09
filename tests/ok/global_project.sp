channel c

abstract a : message
abstract b : message

system out(c,diff(a,b)).

axiom [any] refl (x:message) : x = x.

global goal _ :
  [happens(A)] ->
  [output@A = a] ->
  ([output@A = a] -> equiv(diff(true,false))) ->
  ([happens(A)] -> equiv(diff(output@A,a))) ->
  [output@A = a].
Proof.
  intro A H1 H2 H3.
  (* When projecting we can keep H1: if output@A=a holds for both the left and right
     projections, it also holds for each projection separately.
     We can also keep H3 because its atom are either pure trace formulas (not system
     specific) or equivalence formulas (and the pair annotation is preserved by the
     project tactic).
     We cannot keep H2 because it is not restricted to a trace atom,
     and output@A=a is not a pure trace formula. Indeed, [output@A=a]_{left,right}
     is absurd in models where a<>b, but trivial when considering the left projection
     only. *) 
  project.

  (* Check that H1 is still present. *)
  have _ := H1.
  (* Check that H2 is absent. *) 
  checkfail clear H2 exn HypUnknown. 
  (* Check that H3 is still present. *)
  rewrite equiv H3; 1: by apply A. 
  by apply refl.

  (* Check that H1 is still present. *)
  have _ := H1.
  (* Check that H2 is absent. *)
  checkfail clear H2 exn HypUnknown. 
  (* Check that H3 is still present. *)
  rewrite equiv -H3; 1: by apply A.
  (* Goal should be "false" at this point. *)

Abort.
