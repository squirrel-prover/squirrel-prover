include Real. 
open Real.

(* --------------------------------------------------------- *)
op cst : message.
channel c.

system P = A:out(c,cst).

(* --------------------------------------------------------- *)
(* test of unfolding *)

(* unfold asymptotic local with approximated happens *)
global lemma _ @system:P e :
  [happens A <: e] -> [output@A = cst].
Proof.
  intro H.
  checkfail rewrite /output exn Failure. 
  checkfail expand output exn Failure.
Abort.

(* same as above, in a global setting *)
global lemma _ @system:P e :
  [happens A <: e] -> ([output@A = cst] \/ [false]).
Proof.
  intro H. 
  checkfail rewrite /output exn Failure. 
  checkfail expand output exn Failure.
Abort.

(* unfold asymptotic global with approximated happens *)
global lemma _ @system:P e :
  [happens A <: e] -> [output@A = cst] -> [false].
Proof.
  intro H A. 
  checkfail rewrite /output in A exn Failure. 
  checkfail expand output exn Failure.
Abort.

(* unfold asymptotic global with exact happens *)
global lemma _ @system:P :
  [happens A <: z] -> [output@A = cst] -> [false].
Proof.
  intro H A. 
  rewrite /output in A.
Abort.

(* unfold asymptotic local with exact happens *)
global lemma _ @system:P :
  [happens A <: z] -> [output@A = cst].
Proof.
  intro H.
  rewrite /output.
  apply eq_refl.
Qed.

(* unfold exact global with exact happens *)
global lemma _ @system:P :
  [happens A <: z] -> [output@A = cst <: z] -> [false].
Proof.
  intro H A. 
  rewrite /output in A.
Abort.

(* unfold exact local with exact happens *)
global lemma _ @system:P :
  [happens A <: z] -> [output@A = cst <: z].
Proof.
  intro H.
  rewrite /output.
  apply eq_refl.
Qed.

(* unfold exact global with approximated happens *)
global lemma _ @system:P e :
  [happens A <: e] -> [output@A = cst <: e] -> [false].
Proof.
  intro H A. 
  checkfail rewrite /output in A exn Failure.
  (* FEAT: concrete: we could support this, by paying `e` 
     This does not seem very useful now. *)
Abort.

(* unfold exact local with approximated happens *)
global lemma _ @system:P e :
  [happens A <: e] -> [output@A = cst <: e].
Proof.
  intro H.
  checkfail rewrite /output exn Failure.
  (* FEAT: concrete: same as above *)
Abort.


(* --------------------------------------------------------- *)
(* rewriting a global equality *)

(* approximate rewriting, local conclusion *)
global lemma _ @system:any (x,y:int) e p :
  [x = y] -> [p x <: e].
Proof.
  intro E. 
  checkfail rewrite E exn NothingToRewrite.
Abort.

(* approximate rewriting, global conclusion *)
global lemma _ @system:any (x,y:int) e p :
  [x = y] -> ([p x <: e] /\ [false]).
Proof.
  intro E. 
  checkfail rewrite E exn NothingToRewrite.
Abort.

(* approximate rewriting, global conclusion *)
global lemma _ @system:any (x,y:int) e p :
  ([p x <: e] /\ [p y]) -> [x = y] -> ([p x <: e] /\ [p x]).
Proof.
  intro H E. rewrite E. assumption H.
Qed.

(* exact rewriting, local conclusion *)
global lemma _ @system:any (x,y:int) e p :
  [p y <: e] -> [x = y <: z] -> [p x <: e].
Proof.
  intro H E.
  rewrite E.
  assumption H.
Qed.

(* exact rewriting, global conclusion *)
global lemma _ @system:any (x,y:int) e p :
  ([p y <: e] /\ [p y]) -> [x = y <: z] -> ([p x <: e] /\ [p x]).
Proof.
  intro H E.
  rewrite E.
  assumption H.
Qed.

(* rewriting with error in the conclusion *)
global lemma _ @system:any (x,y:int) e1 e2 p :
  [p y <: e1 - e2] -> 
  [x = y <: e2] -> 
  [p x <: e1].
Proof.
  intro H E.
  rewrite E.
  assumption H.
Qed.

(* rewriting with error in the conclusion *)
global lemma _ @system:any (x,y:int) e1 e2 p :
  [x = y  <: e2] ->
  ([p x <: e1] -> [false <: z]).
Proof.
  intro E. 
  checkfail rewrite E exn NothingToRewrite.
  (* FEAT: concrete: for now, we do not support rewriting in
     non-reachability global formulas. *)
Abort.

(* check that multiplicity of the rewriting is 
   correctly accounted for *)
global lemma _ @system:any (x,y:int) e1 e2 f g (p: int -> bool) :
  [p (g x) && p (g y) <: (e1 - e2) - e2] -> 
  [forall x, f x = g x <: e2] -> 
  [p (f x) && p (f y) <: e1].
Proof.
  intro H E.
  rewrite !E.
  assumption H.
Qed.

(* rewriting with error __in a hypothesis__ *)
global lemma _ @system:any (x,y:int) e1 e2 p :
  [p x <: e1] ->
  [x = y  <: e2] ->
  [p y <: e1 + e2].
Proof.
  intro A E.
  checkfail assumption A exn NotHypothesis.
  rewrite E in A.
  assumption A.
Qed.

(* rewriting with error __in a hypothesis__ *)
global lemma _ @system:any (x,y:int) e1 e2 p :
  ([p x <: e1] -> [false <: z]) ->
  [x = y  <: e2] ->
  [false <: z].
Proof.
  intro A E.
  checkfail rewrite E in A exn NothingToRewrite.
  (* FEAT: concrete: for now, we do not support rewriting in
     non-reachability global hypotheses. *)
Abort.

(* rewriting with error, univeral local quantification *)
global lemma _ @system:any (x,y:int) e1 e2 p (f,g : int -> int) :
  [p (g 42) <: e1 - e2] -> 
  [forall a b, f a = g b <: e2] -> 
  [p (f x) <: e1].
Proof.
  intro H E.
  rewrite (E _ 42).
  assumption H.
Qed.

(* rewriting with error, univeral global quantification *)
global lemma _ @system:any (x,y:int) e1 e2 p (f,g : int -> int) :
  [p (g 42) <: e1 - e2 42] -> 
  (Forall a b, [f a = g b <: e2 b]) -> 
  [p (f x) <: e1].
Proof.
  intro H E.
  rewrite (E _ 42).
  assumption H.
Qed.

(* --------------------------------------------------------- *)
(* rewriting a local equality *)

global lemma _ @system:any (x,y:int) e p :
  [p y <: e] -> [x = y => p x <: e].
Proof.
  intro H; intro E.
  rewrite E.
  assumption H.
Qed.

(* local rewriting in a local hypothesis *)
global lemma _ @system:any (x,y:int) e p :
  [y = 42 => p <: e] ->
  [x = y => x = 42 => p <: e].
Proof.
  intro H.
  intro E A. 
  rewrite E in A.
  revert A => {E}.
  assumption H.
Qed.

(* local rewriting in the bound is not possible *)
global lemma _ @system:any (x,y:int) e p :
  [x = y => p <: e x].
Proof.
  simpl. 
  intro E.
  checkfail rewrite E exn NothingToRewrite.
Abort.

(* local rewriting in a global hypothesis *)
global lemma _ @system:any (x,y:int) e p :
  [x = 42] -> 
  [x = y => p <: e x].
Proof.
  intro A. 
  intro E. 
  checkfail rewrite E in A exn NothingToRewrite.
Abort.

(* --------------------------------------------------------- *)
(* Rewriting in the bound *)

(* Check that we cannot rewrite a local equality in the bound *)
lemma _ @system:any x y p : 
  (x = z) => p <: x + y.
Proof.
  intro E.
  checkfail rewrite E exn NothingToRewrite.
Abort.

(* Check that we can rewrite a global exact equality in the bound *)
global lemma _ @system:any x y p :
  [p <: y] ->
  [x = z <: z] -> [p <: x + y].
Proof.
  intro H E.
  rewrite E.
  simpl.
  assumption H.
Qed.

(*------------------------------------------------------------------*)
(* Rewriting with error __in the bound of an hypothesis__ is not
   allowed. *)
global lemma _ @system:any (x,y:int) e1 e2 p :
  [p <: e1 x] ->
  [x = y  <: e2] ->
  [false].
Proof.
  intro A E.
  checkfail rewrite E in A exn NothingToRewrite.
Abort.

(*------------------------------------------------------------------*)
predicate Exact {set : system} {set: (phi:bool)} = [phi].

(* Rewriting with error __in an exact predicate__ is not
   allowed.
   (For now, we simply disallow concrete rewriting in any atom.) *)
global lemma _ @system:any (x,y:int) e p :
  Exact (p x) ->
  [x = y <: e] ->
  [false].
Proof.
  intro A E. 
  checkfail rewrite E in A exn NothingToRewrite.
Abort.
