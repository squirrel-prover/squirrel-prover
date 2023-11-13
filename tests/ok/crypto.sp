channel c.

include Basic.

(* ========================================================= *)
system [E] null.

(* ========================================================= *)
abstract p : index -> message -> bool
abstract m : index -> message -> message -> message

abstract a : message
abstract b : message

game Bar0 = {
  var l = empty_set;

  oracle g (i : index, x : message) = { 
    l := add x l;
    return m i x (diff(a,b))
  }
}.

game Bar1 = {
  var l = empty_set;

  oracle g (i : index, x : message) = { 
    var old_l = l;
    l := add x l;
    return if not (mem x old_l) then m i x (diff(a,b))
  }
}.

(* ========================================================= *)
global lemma [E] _ (i:index[adv], x : message[adv]) :
  equiv(m i x (diff(a,b))).
Proof.
  crypto Bar0.
Qed.

(* fails if `i` is not adv *)
global lemma [E] _ (i:index, x : message[adv]) :
  equiv(m i x (diff(a,b))).
Proof.
  checkfail crypto Bar0 exn Failure.
Abort.

(* fails if `x` is not adv *)
global lemma [E] _ (i:index[adv], x : message) :
  equiv(m i x (diff(a,b))).
Proof.
  checkfail crypto Bar0 exn Failure.
Abort.

(* --------------------------------------------------------- *)
(* same tests, using `Bar1` *)

global lemma [E] _ (i:index[adv], x : message[adv]) :
  equiv(m i x (diff(a,b))).
Proof.
  crypto Bar1.
Qed.

(* fails if `i` is not adv *)
global lemma [E] _ (i:index, x : message[adv]) :
  equiv(m i x (diff(a,b))).
Proof.
  checkfail crypto Bar1 exn Failure.
Abort.

(* fails if `x` is not adv *)
global lemma [E] _ (i:index[adv], x : message) :
  equiv(m i x (diff(a,b))).
Proof.
  checkfail crypto Bar1 exn Failure.
Abort.

(* --------------------------------------------------------- *)

(* now with two oracle calls and `Bar0` *)
global lemma [E] _ (i,j:index[adv], x,y : message[adv]) :
  equiv(m i x (diff(a,b)), m j y (diff(a,b))).
Proof.
  crypto Bar0.
Qed.

(* same with `Bar1`, must fail since nothing guarantees that `x` and `y` 
   are **always** different.
   Note that this test could be handled if we could generate proof
   obligations for [i <> j] always, instead of overwhelmingly) *)
global lemma [E] _ (i,j:index[adv], x,y : message[adv]) :
  [y <> x] ->
  equiv(m i x (diff(a,b)), m j y (diff(a,b))).
Proof.
  intro H.
  crypto Bar1.
  localize H as H1; clear H.
  assumption H1.
Qed.

name n : index -> message.

(* same as above, again with `Bar1`, but using a name, which we know
   how to handle. *)
global lemma [E] _ (i,j:index[adv], x,y : message[adv]) :
  [i <> j] -> equiv(m i (n i) (diff(a,b)), m j (n j) (diff(a,b))).
Proof.
  intro H.
  crypto Bar1. 
  localize H as H1.
  assumption H1.
Qed.

(* --------------------------------------------------------- *)
(* now with sequences *)

(* succeeds with `Bar0` *)
global lemma [E] _ (i,j:index[adv], x : index -> message[adv]) :
  equiv(fun i => m i (x i) (diff(a,b))).
Proof.
  crypto Bar0.
Qed.

(* with `Bar1`, succeeds using a name, producing a proof obligation *)
global lemma [E] _ (i,j:index[adv], x : index -> message[adv]) :
  [forall (i,i0:index), i0 <> i] ->
  equiv(fun i => m i (n i) (diff(a,b))).
Proof.
  intro H.
  crypto Bar1. 
  localize H as H1. 
  assumption H1. 
Qed.

(* must fail with `Bar1`, since nothing guarantees that all the 
   `x i`s are distinct *)
global lemma [E] _ (i,j:index[adv], x : index -> message[adv]) :
  equiv(fun i => m i (x i) (diff(a,b))).
Proof.
  crypto Bar1.
  checkfail crypto Bar1 exn Failure.
Abort.


(* ========================================================= *)
system [X] !_i in(c,x); out(c, m i x (diff(a,b))).

global lemma [X] _ (tau:timestamp[adv]) :
  [happens(tau)] -> equiv(output@tau).
Proof.
  intro Hap. 
  crypto Bar0.
Qed.

global lemma [X] _ (tau:timestamp[adv]) :
  [happens(tau)] -> equiv(output@tau).
Proof.
  intro Hap. 
  checkfail crypto Bar1 exn Failure.
Abort.

(* ========================================================= *)
(* check that quantifiers over non-ptime enumerable types fail *)

abstract P : message -> bool.

global lemma [E] _ (i:index[adv], x : message[adv]) :
  equiv( (forall x, P x), m i x (diff(a,b))).
Proof.
  checkfail crypto Bar0 exn Failure.
Abort.

global lemma [E] _ (i:index[adv], x : message[adv]) :
  equiv( (exists x, P x), m i x (diff(a,b))).
Proof.
  checkfail crypto Bar0 exn Failure.
Abort.
