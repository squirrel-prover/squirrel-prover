include Real. 
include Int.
open Real.
open Int.

global axiom fooG @system:any : Forall b, [false <: b].

axiom fooL1 @system:any b : false <: b.
axiom fooL2 @system:any   : false <: of_int 42.

(*==================================================================*)
(* `have :` *)

global lemma _ @system:any (b : Real.t) : [false <: of_int 1].
Proof.
  simpl.
  have A : false <: of_int 42 by apply fooL2.
  simpl.
  weak z; 2:auto.
  have B : z <= of_int (-41) by admit.
  assumption B.
Qed.

(*==================================================================*)
(* `have :=` *)

(* test proof-term weakening *)
global lemma _ @system:any (a,b : Real.t) : 
  [a <= b <: z] ->
  [false <: b].
Proof.
  intro H.
  have A := ((fooG a) <: b); 1:assumption H.
  clear H.
  assumption A.
Qed.

global lemma _ @system:any (a,b : Real.t) :
  [a <= b <: z] ->
  [false <: z].
Proof.
  intro H.
  have A := ((fooG a) <: b); 1:assumption H.   
  clear H.
  weak z. { have -> : b = z by admit. auto. }
  assumption A.
Qed.

(*------------------------------------------------------------------*)
global lemma _ @system:any (b : Real.t) : [true <: of_int 1].
Proof.
  simpl.
  have A := fooG.
  weak z; 2:auto.
  have B : z <= of_int 1 by admit.
  assumption B.
Qed.

(*------------------------------------------------------------------*)
(* `fooL1` must be global, because `b` appears in its bound *)
global lemma _ @system:any (b : Real.t) : [true <: of_int 1].
Proof.
  simpl.
  have A := fooL1 (of_int 10).
  weak z; 2:auto.
  have B : z <= of_int 1 by admit.
  assumption B.
Qed.

global lemma _ @system:any (b : Real.t) : [true <: of_int 1].
Proof.
  simpl.
  have A := localize(fooL1 (of_int 10)).
  weak z; 2:auto.
  have B : z <= opp (of_int 9) by admit. 
  revert B; reduce => B.
  assumption B.
Qed.

(*------------------------------------------------------------------*)
(* `fooL2` is local *)
global lemma _ @system:any (b : Real.t) : [true <: of_int 1].
Proof.
  simpl.
  have A := fooL2.
  weak z; 2:auto.
  have B : z <= opp (of_int 41) by admit.
  revert B; reduce => B.
  assumption B.
Qed.
