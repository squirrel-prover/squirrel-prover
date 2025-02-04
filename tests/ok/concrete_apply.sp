include Real. include Int.
open Real. open Int.

op a : bool.
op d : bool.

exact axiom fooA @system:any : a.
exact axiom fooD @system:any : d.

(*==================================================================*)
(* test concrete `apply` tactic, matching in the bound  *)

global lemma _ @system:any p e (u:int) :
  (Forall x, [p x <: e]) ->
  [p u <: e].
Proof.
  intro H.
  apply H.
  auto.
Qed.

global lemma _ @system:any p e (u:int) :
  (Forall x, [p x <: e x]) ->
  [p u <: e u].
Proof.
  intro H.
  apply H.
  auto.
Qed.

global lemma _ @system:any p e (u:int) :
  (Forall x, [p <: e x]) ->
  [p <: e u].
Proof.
  intro H.
  apply H.
  auto.
Qed.

(*------------------------------------------------------------------*)
global lemma _ @system:any p q e (u:int) :
  ([q u <: z]) ->
  (Forall x, [q x => p x <: e]) ->
  [p u <: e].
Proof.
  intro Ax H.
  apply H.
  assumption Ax.
Qed.

global lemma _ @system:any q p e (u:int) :
  ([q u <: z]) ->
  (Forall x, [q x => p x <: e x]) ->
  [p u <: e u].
Proof.
  intro Ax H.
  apply H.
  assumption Ax.
Qed.

global lemma _ @system:any q p e (u:int) :
  ([q u <: z]) ->
  (Forall x, [q x => p <: e x]) ->
  [p <: e u].
Proof.
  intro Ax H.
  apply H.
  assumption Ax.
Qed.

(*------------------------------------------------------------------*)
global lemma _ @system:any p q e (u:int) :
  ([q u <: z]) ->
  (Forall x, [q x] -> [p x <: e]) ->
  [p u <: e].
Proof.
  intro Ax H.
  apply H.
  assumption Ax.
  by true.
Qed.

global lemma _ @system:any q p e (u:int) :
  ([q u <: z]) ->
  (Forall x, [q x] -> [p x <: e x]) ->
  [p u <: e u].
Proof.
  intro Ax H.
  apply H.
  assumption Ax.
  by true.
Qed.

global lemma _ @system:any q p e (u:int) :
  ([q u <: z]) ->
  (Forall x, [q x] -> [p <: e x]) ->
  [p <: e u].
Proof.
  intro Ax H.
  apply H.
  assumption Ax.
  by true.
Qed.

(*------------------------------------------------------------------*)
global lemma _ @system:any p e :
  [p <: e] ->
  [p].
Proof.
  intro H.
  checkfail apply H exn Failure. (* not an asymptotic goal *)
Abort.

global lemma _ @system:any p :
  [p <: z] ->
  [p].
Proof.
  intro H.
  apply H.
Qed.

(*------------------------------------------------------------------*)
(* local apply in a concrete judgement *)

global lemma _ @system:any p q e :
  [p <: e] ->
  [(p => q) => q <: e].
Proof.
  intro Ax.
  intro H.
  apply H.
  assumption Ax.
Qed.

global lemma _ @system:any p q (u,v : int) e :
  [p u <: e] ->
  [p v <: e] ->
  [(forall x, p x => q x) => q u <: e].
Proof.
  intro Ax1 Ax2.
  intro H.
  apply H. 
  checkfail assumption Ax2 exn NotHypothesis.
  assumption Ax1.
Qed.


(*------------------------------------------------------------------*)
global lemma _ @system:any p q r (eH, eP, eQ:Real.t)  :
  [p <: z] ->
  [q <: z] ->
  [p => q => r <: eH] ->
  [r <: eH].
Proof.
  intro P Q H.
  apply H.

  (* In the concrete logic, hypothesis of the 
     applied lemma are put in conjunction, to 
     let the user split the error mass as they
     want. *)
  reduce; split.
  + assumption P.
  + assumption Q.  
Qed.

(*==================================================================*)
(* test concrete `apply` tactic, discharging the bound  *)

global lemma _ @system:any r (e1, e2:Real.t)  :
  [z <= e2 - e1 <: z] ->
  [r <: e1] ->
  [r <: e2].
Proof.
  intro A H.
  apply H. 
  true.
  assumption A. 
Qed.

(*------------------------------------------------------------------*)
global lemma _ @system:any p q r (eH, eP, eQ:Real.t)  :
  [p <: eP] ->
  [q <: eQ] ->
  [p => q => r <: eH] ->
  [r <: eH + eP + eQ].
Proof.
  intro P Q H.
  apply H. 
  split eP. 
  + assumption P.
  + apply Q. 
    true.
    have -> : ((((eH + eP) + eQ) - eH) - eP) - eQ = z by admit.
    auto.
Qed.

(*------------------------------------------------------------------*)
global lemma _ @system:any p e1 e2 (u:int) :
  [z <= e2 - (e1 u) <: z] ->
  (Forall x, [p <: e1 x]) ->
  [p <: e2].
Proof.
  intro A H.
  checkfail apply H exn Failure.
  apply H u.
  true. 
  assumption A. 
Qed.

(*------------------------------------------------------------------*)
global lemma _ @system:any (e1, e2 : Real.t) a b :
  ([a <: e1] -> [b <: e2]) -> [a <: e1] -> [b <: e2].
Proof.
  nosimpl intro G H.
  nosimpl have Q := G H.
  assumption Q.
Qed.

(*------------------------------------------------------------------*)
global lemma _ @system:any (e1, e2, eH : Real.t) a b :
  [eH <= e1 <: z] -> ([a <: e1] -> [b <: e2]) -> [a <: eH] -> [b <: e2].
Proof.
  intro B G H. 
  have Q := G H.
  + assumption B.
  + assumption Q.
Qed.

global lemma _ @system:any (e1, e2, eH : Real.t) a b :
  ([a => b <: e1]) -> [a <: eH] -> [false <: z].
Proof.
  intro G H.
  checkfail have Q := G H exn Failure.  (* should fail *)
Abort.

global lemma _ @system:any (e1, e2, eH : Real.t) a b :
  ([a => b <: e1]) -> [a <: eH] -> [b <: e1 + eH].
Proof.
  intro G H.
  have Q := (localize(G)) %( localize(H)).
  clear G H.
  assumption Q.
Qed.

global lemma _ @system:any (e1, e2, eH : Real.t) a b :
  ([a => b <: e1]) -> [a <: eH] -> [b <: e1 + eH].
Proof.
  intro G H.
  have Q := (localize(G)) H. 
  clear G H.
  assumption Q.
Qed.

global lemma _ @system:any (e1, e2, eH : Real.t) a b :
  ([a => b <: e1]) -> [a <: eH] -> [b <: e1 + eH].
Proof.
  intro G H.
  have Q := G %(localize(H)). 
  assumption Q.
Qed.
