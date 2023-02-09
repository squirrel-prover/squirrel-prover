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

global goal _ (tau:timestamp) : 
  [p(n)=true] /\ [p(n)=false] -> [p(n)=true && p(n)=false].
Proof.
  intro [H1 H2].
  split.
  + apply H1.
  + apply H2.
Qed.

global goal _ (tau:timestamp) : 
  [p(n)=true && p(n)=false] -> [p(n)=true] /\ [p(n)=false].
Proof.
  intro [H1 H2].
  split.
  + apply H1.
  + apply H2.
Qed.

global goal _ (tau:timestamp) : 
  [f(n)=a && f(n)=b && f(n)=c] -> [f(n)=a] /\ [f(n)=b] /\ [f(n)=c].
Proof.
  intro [H1 H2 H3].
  by repeat split.
Qed.

(* ================ IMPLICATION ================ *)

(* Cannot move local implication to global level if left subformula isn't 
   deterministic. *)
global goal _ (tau:timestamp) : [p(n)=true => happens(tau)].
Proof.
  checkfail intro H exn NothingToIntroduce.
Abort.

(* Cannot move local implication to global level if left subformula is not 
   deterministic. *)
global goal _ (tau:timestamp) : [happens(tau) => p(n)=true].
Proof.
  checkfail intro H exn NothingToIntroduce.
Abort.

(* Can move local implication to global level if left subformula is deterministic
   and system-independent. *)
global goal _ (tau:timestamp[const]) : [happens(tau) => p(n)=true].
Proof.
  intro H.
Abort.

(*------------------------------------------------------------------*)
(* Ternary variant. *)
global goal _ : [false => false => p(n)=true].
Proof.
  intro H1 H2.
Abort.

(* Ternary variant, all formulas det + si. *)
global goal _ : [false => false => false].
Proof.
  intro H1 H2.
Abort.

(* ================ DISJUNCTION ================ *)

(* Local disjunction can be made global when one of its terms are deterministic. *)

global goal _ (tau:timestamp) :
  [happens(tau) || p(n)=true] -> [false].
Proof.
  (* Tactic failed: not a disjunction *)
  checkfail intro [H1|H2] exn Failure.
Abort.

global goal _ (tau:timestamp[const]) :
  [happens(tau) || p(n)=true] -> [false].
Proof.
  intro [H1|H2].
Abort.

global goal _ (tau:timestamp) :
  [p(n)=true || happens(tau)] -> [false].
Proof.
  (* Tactic failed: not a disjunction *)
  checkfail intro [H1|H2] exn Failure.
Abort.

global goal _ (tau:timestamp[const]) :
  [p(n)=true || happens(tau)] -> [false].
Proof.
  intro [H1|H2].
Abort.

(*------------------------------------------------------------------*)
(* It cannot be moved to the global level if both terms are probabilistic. *)

global goal _ (tau:timestamp) :
  [p(n)=true || p(n)=false] -> [false].
Proof.
  (* Tactic failed: not a disjunction *)
  checkfail intro [H1|H2] exn Failure.
Abort.

(*------------------------------------------------------------------*)
(* Ternary variant, pure formula only in first position. *)

global goal _ : [false || p(n)=true || p(n)=false] -> [false].
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

global goal _ : [p(n)=false || p(n)=true || true] -> [false].
Proof.
  (* Tactic failed: not a disjunction *) 
  checkfail intro [_|_] exn Failure.
Abort.

(*------------------------------------------------------------------*)
(* Ternary variant, pure formula in second position. *)

global goal _ : [p(n)=false || true || p(n)=true] -> [false].
Proof.
  (* Tactic failed: not a disjunction *) 
  checkfail intro [_|_] exn Failure.
Abort.

(*------------------------------------------------------------------*)
(* Ternary variant, pure formula in two positions. *)

global goal _ : [false || true || p(n)=true] -> [false].
Proof.
  intro [_|_|_].
Abort.

global goal _ : [false || p(n)=true || true] -> [false].
Proof.
  intro [_|_|_].
Abort.

global goal _ : [p(n)=true || false || true] -> [false].
Proof.
  intro [_|_|_].
Abort.

(*------------------------------------------------------------------*)
(* Ternary variant, only pure subformulas. *)

global goal _ : [false || false || false] -> [false].
Proof.
  intro [_|_|_].
Abort.

(*------------------------------------------------------------------*)
(* Ternary variant, no pure subformulas. *)

global goal _ : [p(n)=true || true=p(n) || p(n)=false] -> [false].
Proof.
  (* Tactic failed: not a disjunction *) 
  checkfail intro [_|_] exn Failure.
Abort.

(* ================ NEGATION ================ *)

global goal _ : [not(p(n)=true)].
Proof.
  checkfail intro _ exn NothingToIntroduce.
Abort.

(* ================ QUANTIFICATION ================ *)

(* Universal quantification can always be made global. *)
global goal _ : 
  [forall (i:index), q(n,i) = true] -> Forall (i:index), [q(n,i)=true].
Proof.
  nosimpl intro H.
  nosimpl intro i.
  nosimpl have _ := H i.
  assumption.
Qed.

(*------------------------------------------------------------------*)
(* Existential quantification cannot be made global if body is probabilistic. *)
global goal _ : [exists (i:index) q(n,i) = true] -> [false].
Proof. 
  (* Tactic failed: cannot destruct *)
  checkfail intro [i H] exn Failure.
Abort.

global goal _ (t0 : timestamp): [exists (t:timestamp), t = t0] -> [false].
Proof.
  (* Tactic failed: cannot destruct *)
  checkfail intro [i H] exn Failure.
Abort.

(*------------------------------------------------------------------*)
(* Existential quantification can be made global if body is deterministic + SI. *)
global goal _ : [exists (i:index), false] -> [false].
Proof.
  intro [i H].
Abort.

(* here, the body is deterministic, and is SI because there is only one system being 
   considered *)
global goal [set:default/left; equiv:default/left,default/left] 
  _ (t0 : timestamp[const]): 
  [exists (t:timestamp), t = t0] -> [false].
Proof.
  intro [i H].
Abort.

(* the body is deterministic, but not SI (because several systems are considered in 
   the set and equiv part) *)
global goal [set:default/left, default/right; equiv:default] 
  _ (t0 : timestamp[const]): 
  [exists (t:timestamp), t = t0] -> [false].
Proof.
   (* Tactic failed: cannot destruct *)
  checkfail intro [i H] exn Failure.

   (* idem *)
  checkfail intro H; destruct H as [i H] exn Failure. 
Abort.

(* bis, changing how the system is given *)
global goal [set:default/left, default/right; equiv:default/left,default/right] 
  _ (t0 : timestamp[const]): 
  [exists (t:timestamp), t = t0] -> [false].
Proof.
   (* Tactic failed: cannot destruct *)
  checkfail intro [i H] exn Failure.

   (* idem *)
  checkfail intro H; destruct H as [i H] exn Failure. 
Abort.

(* the body is deterministic, but not SI (because several systems are considered 
   in the set part) *)
global goal [set:default/left, default/right; equiv:default/left,default/left] 
  _ (t0 : timestamp[const]): 
  [exists (t:timestamp), t = t0] -> [false].
Proof.
   (* Tactic failed: cannot destruct *)
  checkfail intro [i H] exn Failure.
Abort.

(* the body is deterministic, but not SI (because several systems are considered in 
   the equiv part) *)
global goal [set:default/left; equiv:default/left,default/right] 
  _ (t0 : timestamp[const]): 
  [exists (t:timestamp), t = t0] -> [false].
Proof.
   (* Tactic failed: cannot destruct *)
  checkfail intro [i H] exn Failure.
Abort.

(* bis, changing how the system is given *)
global goal [set:default/left; equiv:default] 
  _ (t0 : timestamp[const]): 
  [exists (t:timestamp), t = t0] -> [false].
Proof.
   (* Tactic failed: cannot destruct *)
  checkfail intro [i H] exn Failure.
Abort.

