open Real.

channel c.

system P = A:out(c,empty); B: out(c,empty).

(*------------------------------------------------------------------*)
(* *) axiom hap  @system:P : happens(B).
exact axiom hapE @system:P : happens(B).

(* *) axiom conc  @system:P : A < B => false.
exact axiom concE @system:P : A < B => false.

global axiom Gconc  @system:P : [A < B] -> [false].
global axiom Gconc1 @system:P : [A < B] -> [false <: z].
global axiom Gconc2 @system:P : [A < B <: z] -> [false <: z].

(*------------------------------------------------------------------*)
lemma _ @system:P : false.
Proof.
  depends A,B. 
  + apply hap.
  + apply conc.
Qed.

(*------------------------------------------------------------------*)
exact lemma _ @system:P : false.
Proof.
  depends A,B. 
  + checkfail apply hap exn Failure. apply hapE.
  + checkfail apply conc exn Failure. apply concE.
Qed.

(*------------------------------------------------------------------*)
global lemma _ @system:P : [false].
Proof.
  depends A,B. 
  + apply hap.
  + apply Gconc.
Qed.

(*------------------------------------------------------------------*)
global lemma _ @system:P : [false <: z].
Proof.
  depends A,B. 
  + apply hap.
  + checkfail apply Gconc exn ApplyMatchFailure. apply Gconc1.
Qed.
