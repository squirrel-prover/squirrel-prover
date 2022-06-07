abstract p : message -> boolean.
abstract q : message -> index -> boolean.

abstract f : message -> message.
abstract a : message.
abstract b : message.
abstract c : message.

name n : message.

system null.

(* ================ CONJUNCTION ================ *)

(* [phi&&psi] is always equivalent to [phi]/\[psi] *)

global goal _ (tau:timestamp) : [p(n)=true] /\ [p(n)=false] -> [p(n)=true && p(n)=false].
Proof.
  intro [H1 H2].
  split.
  + apply H1.
  + apply H2.
Qed.

global goal _ (tau:timestamp) : [p(n)=true && p(n)=false] -> [p(n)=true] /\ [p(n)=false].
Proof.
  intro [H1 H2].
  split.
  + apply H1.
  + apply H2.
Qed.

global goal _ (tau:timestamp) : [f(n)=a && f(n)=b && f(n)=c] -> [f(n)=a] /\ [f(n)=b] /\ [f(n)=c].
Proof.
  intro [H1 H2 H3].
  by repeat split.
Qed.

(* ================ IMPLICATION ================ *)

(* Cannot move local implication to global level if left subformula isn't pure. *)
global goal _ (tau:timestamp) : [p(n)=true => happens(tau)].
Proof.
  checkfail intro H exn NothingToIntroduce.
Abort.

(* Can move local implication to global level if left subformula is pure. *)
global goal _ (tau:timestamp) : [happens(tau) => p(n)=true].
Proof.
  intro H.
Abort.

(* Ternary variant. *)
global goal _ : [False => False => p(n)=true].
Proof.
  intro H1 H2.
Abort.

(* Ternary variant, all formulas pure. *)
global goal _ : [False => False => False].
Proof.
  intro H1 H2.
Abort.

(* ================ DISJUNCTION ================ *)

(* Local disjunction can be made global when one of its terms are deterministic. *)

global goal _ (tau:timestamp) :
  [happens(tau) || p(n)=true] -> [False].
Proof.
  intro [H1|H2].
Abort.

global goal _ (tau:timestamp) :
  [p(n)=true || happens(tau)] -> [False].
Proof.
  intro [H1|H2].
Abort.

(* It cannot be moved to the global level if both terms are probabilistic. *)

global goal _ (tau:timestamp) :
  [p(n)=true || p(n)=false] -> [False].
Proof.
  checkfail intro [H1|H2] exn Failure.
Abort.

(* Ternary variant, pure formula only in first position. *)

global goal _ : [False || p(n)=true || p(n)=false] -> [False].
Proof.
  checkfail intro [H1|H2|H3] exn Failure.
  intro [H1|H2].
  + admit.
  + checkfail destruct H2 as [_|_] exn Failure.
Abort.

(* Ternary variant, pure formula in last position. *)

global goal _ : [p(n)=False || p(n)=true || True] -> [False].
Proof.
  checkfail intro [_|_] exn Failure.
Abort.

(* Ternary variant, pure formula in second position. *)

global goal _ : [p(n)=False || True || p(n)=true] -> [False].
Proof.
  checkfail intro [_|_] exn Failure.
Abort.

(* Ternary variant, pure formula in two positions. *)

global goal _ : [False || True || p(n)=true] -> [False].
Proof.
  intro [_|_|_].
Abort.

global goal _ : [False || p(n)=true || True] -> [False].
Proof.
  intro [_|_|_].
Abort.

global goal _ : [p(n)=true || False || True] -> [False].
Proof.
  intro [_|_|_].
Abort.

(* Ternary variant, only pure subformulas. *)

global goal _ : [False || False || False] -> [False].
Proof.
  intro [_|_|_].
Abort.

(* Ternary variant, no pure subformulas. *)

global goal _ : [p(n)=true || true=p(n) || p(n)=false] -> [False].
Proof.
  checkfail intro [_|_] exn Failure.
Abort.

(* ================ NEGATION ================ *)

global goal _ : [not(p(n)=true)].
Proof.
  checkfail intro _ exn NothingToIntroduce.
Abort.

(* ================ QUANTIFICATION ================ *)

(* Universal quantification can always be made global. *)
global goal _ : [forall (i:index) q(n,i) = true] -> forall (i:index) [q(n,i)=true].
Proof.
  nosimpl intro H.
  nosimpl intro i.
  nosimpl have _ := H i.
  assumption.
Qed.

(* Existential quantification cannot be made global if body is probabilistic. *)
global goal _ : [exists (i:index) q(n,i) = true] -> [False].
Proof.
  checkfail intro [i H] exn Failure.
Abort.

(* Existential quantification can be made global if body is deterministic. *)
global goal _ : [exists (i:index) False] -> [False].
Proof.
  intro [i H].
Abort.
