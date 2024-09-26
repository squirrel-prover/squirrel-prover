abstract p : message -> boolean.
abstract q : message * index -> boolean.

abstract f : message -> message.
abstract a : message.
abstract b : message.
abstract c : message.

name n : message.

system null.

(* ================ CONJUNCTION ================ *)

(* [phi&&psi] is always equivalent to [phi]/\[psi] *)

global lemma _ (tau:timestamp) : 
  [p(n)=true] /\ [p(n)=false] -> [p(n)=true && p(n)=false].
Proof.
  intro [H1 H2].
  split.
  + apply H1.
  + apply H2.
Qed.

global lemma _ (tau:timestamp) : 
  [p(n)=true && p(n)=false] -> [p(n)=true] /\ [p(n)=false].
Proof.
  intro [H1 H2].
  split.
  + apply H1.
  + apply H2.
Qed.

global lemma _ (tau:timestamp) : 
  [f(n)=a && f(n)=b && f(n)=c] -> [f(n)=a] /\ [f(n)=b] /\ [f(n)=c].
Proof.
  intro [H1 H2 H3].
  by repeat split.
Qed.

(* ================ IMPLICATION ================ *)

(* Cannot move local implication to global level if left subformula isn't 
   constant. *)
global lemma _ (tau:timestamp) : [p(n)=true => happens(tau)].
Proof.
  checkfail intro H exn NothingToIntroduce.
Abort.

(* Cannot move local implication to global level if left subformula 
   isn't constant. *)
global lemma _ (tau:timestamp) : [happens(tau) => p(n)=true].
Proof.
  checkfail intro H exn NothingToIntroduce.
Abort.

(* Can move local implication to global level if left subformula is constant
   and system-independent. *)
global lemma _ (tau:timestamp[const]) : [happens(tau) => p(n)=true].
Proof.
  intro H.
Abort.

(*------------------------------------------------------------------*)
(* Ternary variant. *)
global lemma _ : [false => false => p(n)=true].
Proof.
  intro H1 H2.
Abort.

(* Ternary variant, all formulas constant + si. *)
global lemma _ : [false => false => false].
Proof.
  intro H1 H2.
Abort.

(* ================ DISJUNCTION ================ *)

(* Local disjunction can be made global when one of its terms are constant. *)

global lemma _ (tau:timestamp) :
  [happens(tau) || p(n)=true] -> [false].
Proof.
  (* Tactic failed: not a disjunction *)
  checkfail intro [H1|H2] exn Failure.
Abort.

global lemma _ (tau:timestamp[const]) :
  [happens(tau) || p(n)=true] -> [false].
Proof.
  intro [H1|H2].
Abort.

global lemma _ (tau:timestamp) :
  [p(n)=true || happens(tau)] -> [false].
Proof.
  (* Tactic failed: not a disjunction *)
  checkfail intro [H1|H2] exn Failure.
Abort.

global lemma _ (tau:timestamp[const]) :
  [p(n)=true || happens(tau)] -> [false].
Proof.
  intro [H1|H2].
Abort.

(*------------------------------------------------------------------*)
(* It cannot be moved to the global level if both terms are probabilistic. *)

global lemma _ (tau:timestamp) :
  [p(n)=true || p(n)=false] -> [false].
Proof.
  (* Tactic failed: not a disjunction *)
  checkfail intro [H1|H2] exn Failure.
Abort.

(*------------------------------------------------------------------*)
(* Ternary variant, pure formula only in first position. *)

global lemma _ : [false || p(n)=true || p(n)=false] -> [false].
Proof.
  (* Tactic failed: not a disjunction *) 
  checkfail intro [H1|H2|H3] exn Failure.
  intro [H1|H2].
  + admit.
  (* Tactic failed: not a disjunction *) 
  + checkfail destruct H2 as [_|_] exn Failure.
Abort.

(*------------------------------------------------------------------*)
(* Ternary variant, pure formula in last position. *)

global lemma _ : [p(n)=false || p(n)=true || true] -> [false].
Proof.
  (* Tactic failed: not a disjunction *) 
  checkfail intro [_|_] exn Failure.
Abort.

(*------------------------------------------------------------------*)
(* Ternary variant, pure formula in second position. *)

global lemma _ : [p(n)=false || true || p(n)=true] -> [false].
Proof.
  (* Tactic failed: not a disjunction *) 
  checkfail intro [_|_] exn Failure.
Abort.

(*------------------------------------------------------------------*)
(* Ternary variant, pure formula in two positions. *)

global lemma _ : [false || true || p(n)=true] -> [false].
Proof.
  intro [_|_|_].
Abort.

global lemma _ : [false || p(n)=true || true] -> [false].
Proof.
  intro [_|_|_].
Abort.

global lemma _ : [p(n)=true || false || true] -> [false].
Proof.
  intro [_|_|_].
Abort.

(*------------------------------------------------------------------*)
(* Ternary variant, only pure subformulas. *)

global lemma _ : [false || false || false] -> [false].
Proof.
  intro [_|_|_].
Abort.

(*------------------------------------------------------------------*)
(* Ternary variant, no pure subformulas. *)

global lemma _ : [p(n)=true || true=p(n) || p(n)=false] -> [false].
Proof.
  (* Tactic failed: not a disjunction *) 
  checkfail intro [_|_] exn Failure.
Abort.

(* ================ NEGATION ================ *)

global lemma _ : [not(p(n)=true)].
Proof.
  checkfail intro _ exn NothingToIntroduce.
Abort.

(* ================ QUANTIFICATION ================ *)

(* Universal quantification can always be made global. *)
global lemma _ : 
  [forall (i:index), q(n,i) = true] -> Forall (i:index), [q(n,i)=true].
Proof.
  nosimpl intro H.
  nosimpl intro i.
  nosimpl have _ := H i.
  assumption.
Qed.

(*------------------------------------------------------------------*)
(* Existential quantification can be made global, even if the body is
   probabilistic (because the introduced variable is also probabilistic). *)
global lemma _ : [exists (i:index), q(n,i) = true] -> [false].
Proof. 
  intro [i H].
Abort.

global lemma _ (t0 : timestamp): [exists (t:timestamp), t = t0] -> [false].
Proof.
  intro [i H].
Abort.

(*------------------------------------------------------------------*)
(* Existential quantification can be made global if body is constant + SI. *)
global lemma _ : [exists (i:index), false] -> [false].
Proof.
  intro [i H].
Abort.

(* here, the body is constant, and is SI because there is only one system being 
   considered *)
global lemma [set:default/left; equiv:default/left,default/left] 
  _ (t0 : timestamp[const]): 
  [exists (t:timestamp), t = t0] -> [false].
Proof.
  intro [i H].
Abort.

global axiom [set:any; equiv:default] foo (x : timestamp[glob]) : [false].

(* the body is constant, but not SI (because several systems are considered in 
   the set and equiv part) *)
global lemma [set:default/left, default/right; equiv:default] 
  _ (t0 : timestamp[const]): 
  [exists (t:timestamp), t = t0] -> [false].
Proof.
  intro [t H]. (* we can introduce `t`, but it is not `glob`, which we check below *)
  checkfail have ? := foo t exn Failure. 
Abort.

(* bis, changing how the system is given *)
global lemma [set:default/left, default/right; equiv:default/left,default/right] 
  _ (t0 : timestamp[const]): 
  [exists (t:timestamp), t = t0] -> [false].
Proof.
  intro [t H]. (* we can introduce `t`, but it is not `glob`, which we check below *)
  checkfail have ? := foo t exn Failure. 
Abort.

(* the body is constant, but not SI (because several systems are considered 
   in the set part) *)
global lemma [set:default/left, default/right; equiv:default/left,default/left] 
  _ (t0 : timestamp[const]): 
  [exists (t:timestamp), t = t0] -> [false].
Proof.
  intro [t H]. (* we can introduce `t`, but it is not `glob`, which we check below *)
  checkfail have ? := foo t exn Failure. 
Abort.

(* the body is constant, but not SI (because several systems are considered in 
   the equiv part) *)
global lemma [set:default/left; equiv:default/left,default/right] 
  _ (t0 : timestamp[const]): 
  [exists (t:timestamp), t = t0] -> [false].
Proof.
  intro [t H]. (* we can introduce `t` *)
  (* `t` could be `glob` here, as we are in a single system.
     Curently, Squirrel does not see it *)
  checkfail have ? := foo t exn Failure. 
Abort.

(* bis, changing how the system is given *)
global lemma [set:default/left; equiv:default] 
  _ (t0 : timestamp[const]): 
  [exists (t:timestamp), t = t0] -> [false].
Proof.
  intro [t H]. (* we can introduce `t` *)
  (* `t` could be `glob` here, as we are in a single system.
     Curently, Squirrel does not see it *)
  checkfail have ? := foo t exn Failure. 
Abort.

