include Real. 
open Real.

op m1 : message.

channel c.
process A = out(c, m1).

system sys = A. 

(*------------------------------------------------------------------*)
(* *) axiom fooA @system:any : m1 = witness.
exact axiom fooE @system:any : m1 = witness.

(*------------------------------------------------------------------*)
global lemma [sys] _ : [happens(A)] -> [output@A = m1]. 
Proof.
  intro H1. auto. 
Qed.

(*------------------------------------------------------------------*)
(* Same as above, but the conclusion is exact (thus, the `happens`
   hypothesis cannot be used). *)
global lemma [sys] _ : [happens(A)] -> [output@A = m1 <: z]. 
Proof.
  intro H1. 

  (* `auto` cannot conclude *)
  checkfail auto exn GoalNotClosed.

  (* we cannot manually expand `output` *)
  checkfail rewrite /output exn Failure.
  checkfail expand output exn Failure.

  (* `reduce` cannot reduce `output` either *)
  reduce ~delta. 
  checkfail auto exn GoalNotClosed. 

  (* `smt` should fail *)
  checkfail (smt ~steps:10000) exn Failure. 
Abort.

(*==================================================================*)
(* happens hypothesis: `asymptotic`
   target            : `asymptotic` *)

global lemma [sys] _ : [happens(A)] -> [output@A = witness].
Proof.
  intro H1. rewrite fooA. clear H1. auto.
Qed.

global lemma [sys] _ : [happens(A)] -> [output@A = witness].
Proof.
  intro H1. rewrite fooE. clear H1. auto.
Qed.

(*------------------------------------------------------------------*)
(* happens hypothesis: `exact`
   target            : `asymptotic` *)

global lemma [sys] _ : [happens(A) <: z] -> [output@A = witness].
Proof.
  intro H1. rewrite fooA. clear H1. auto. 
Qed.

global lemma [sys] _ : [happens(A) <: z] -> [output@A = witness].
Proof.
  intro H1. rewrite fooE. clear H1. auto. 
Qed.

(*------------------------------------------------------------------*)
(* happens hypothesis: `concrete`
   target            : `asymptotic` *)

global lemma [sys] _ e : [happens(A) <: e] -> [output@A = witness].
Proof.
  intro H1. checkfail rewrite fooA exn NothingToRewrite. 
Abort.

global lemma [sys] _ e : [happens(A) <: e] -> [output@A = witness].
Proof.
  intro H1. checkfail rewrite fooE exn NothingToRewrite. 
Abort.

(*------------------------------------------------------------------*)
(* happens hypothesis: `asymptotic`
   target            : `exact` *)

global lemma [sys] _ : [happens(A)] -> [output@A = witness <: z].
Proof.
  intro H1. checkfail rewrite fooA exn NothingToRewrite. 
Abort.

global lemma [sys] _ : [happens(A)] -> [output@A = witness <: z].
Proof.
  intro H1. checkfail rewrite fooE exn NothingToRewrite. 
Abort.

(*------------------------------------------------------------------*)
(* happens hypothesis: `asymptotic`
   target            : `concrete` *)

global lemma [sys] _ e : [happens(A)] -> [output@A = witness <: e].
Proof.
  intro H1. checkfail rewrite fooA exn NothingToRewrite. 
Abort.

global lemma [sys] _ e : [happens(A)] -> [output@A = witness <: e].
Proof.
  intro H1. checkfail rewrite fooE exn NothingToRewrite. 
Abort.

(*------------------------------------------------------------------*)
(* happens hypothesis: `exact`
   target            : `exact` *)

global lemma [sys] _ : [happens(A) <: z] -> [output@A = witness <: z].
Proof.
  intro H1. checkfail rewrite fooA exn NothingToRewrite. 
Abort.

global lemma [sys] _ : [happens(A) <: z] -> [output@A = witness <: z].
Proof.
  intro H1. rewrite fooE. clear H1. auto. 
Qed.

(*------------------------------------------------------------------*)
(* happens hypothesis: `exact`
   target            : `concrete` *)

global lemma [sys] _ e : [happens(A) <: z] -> [output@A = witness <: e].
Proof.
  intro H1. checkfail rewrite fooA exn NothingToRewrite. 
Abort.

global lemma [sys] _ e : [happens(A) <: z] -> [output@A = witness <: e].
Proof.
  intro H1. rewrite fooE. clear H1. weak z; 1:admit. auto. 
Qed.

(*------------------------------------------------------------------*)
(* happens hypothesis: `concrete`
   target            : `concrete` *)

global lemma [sys] _ e1 e2 : [happens(A) <: e1] -> [output@A = witness <: e2].
Proof.
  intro H1. checkfail rewrite fooA exn NothingToRewrite. 
Abort.

global lemma [sys] _ e1 e2 : [happens(A) <: e1] -> [output@A = witness <: e2].
Proof.
  intro H1. checkfail rewrite fooE exn NothingToRewrite. 
Abort.

(*==================================================================*)
global lemma [sys] _ : [happens(A)] -> [output@A = witness] -> [m1 = witness]. 
Proof.
  intro H1 H2. 
  rewrite /output in H2.
  clear H1.
  assumption H2.
Qed.

(*------------------------------------------------------------------*)
global lemma [sys] _ e : 
  [happens(A) <: z] -> [output@A = witness <: e] -> 
  [m1 = witness <: e]. 
Proof.
  intro H1 H2. 
  rewrite /output in H2.
  clear H1.
  assumption H2.
Qed.

(*------------------------------------------------------------------*)
global lemma [sys] _ : 
  [happens(A) <: z] -> [output@A = witness] -> 
  [m1 = witness]. 
Proof.
  intro H1 H2. 
  rewrite /output in H2.
  clear H1.
  assumption H2.
Qed.

(*------------------------------------------------------------------*)
global lemma [sys] _ e : 
  [happens(A)] -> [output@A = witness <: e] -> 
  [m1 = witness <: e]. 
Proof.
  intro H1 H2. 
  checkfail rewrite /output in H2 exn Failure.
Abort.

(*==================================================================*)
global lemma [sys] _ : [happens(A)] -> [output@A = witness] -> [m1 = witness]. 
Proof.
  intro H1.
  reduce ~delta.
  intro {H1} H. 
  assumption H.
Qed.

(*------------------------------------------------------------------*)
global lemma [sys] _ e : 
  [happens(A) <: z] -> [output@A = witness <: e] -> 
  [m1 = witness <: e]. 
Proof.
  intro H1.
  reduce ~delta.
  intro {H1} H. 
  assumption H.
Qed.

(*------------------------------------------------------------------*)
global lemma [sys] _ : 
  [happens(A) <: z] -> [output@A = witness] -> 
  [m1 = witness]. 
Proof.
  intro H1.
  reduce ~delta.
  intro {H1} H. 
  assumption H.
Qed.

(*------------------------------------------------------------------*)
global lemma [sys] _ : 
  [happens(A)] -> [output@A = witness] -> 
  [m1 = witness]. 
Proof.
  intro H1.
  reduce ~delta.
  intro {H1} H. 
  assumption H.
Qed.

(*------------------------------------------------------------------*)
global lemma [sys] _ e : 
  [happens(A)] -> [output@A = witness <: e] -> 
  [m1 = witness <: e]. 
Proof.
  intro H1.
  reduce ~delta.
  intro {H1} H. 
  checkfail assumption H exn NotHypothesis.
Abort.
