include Core.
include Int.
open Int.

channel c.

op format ['a] : 'a -> message.
op a : message.
op b : message.

(*------------------------------------------------------------------*)
system P = !_i in(c,x); A: out(c,x); !_j B:out(c,x) | D: out(c,empty).

(*------------------------------------------------------------------*)
name k  : message.
name k' : message.

let m : message = k.

lemma [any] _ : m = k.
Proof.
  rewrite /m.
  apply eq_refl.
Qed.

lemma _ @system:P : diff(m,empty) = diff(k,empty).
Proof.
  rewrite /m.
  apply eq_refl.
Qed.

(*------------------------------------------------------------------*)
(* testing the `fresh` tactic *)

lemma _ @system:P : m = k => false.
Proof.
  intro H. 
  checkfail by fresh H exn GoalNotClosed.
Abort.

lemma _ @system:P : m = k' => false.
Proof.
  intro H. 
  fresh H.
Qed.

(*==================================================================*)
let m' x : message = <k,x>.

lemma [any] _ : m' empty = <k,empty>.
Proof.
  rewrite /m'.
  apply eq_refl.
Qed.

(*==================================================================*)
(* testing the `fresh` tactic *)

name kk : index -> message.

let u i : message = kk i.

lemma _ @system:P i j : i <> j => u i = kk j => false.
Proof.
  intro Eq H. 
  fresh H.
  auto.
Qed.

lemma _ @system:P i : u i = kk i => false.
Proof.
  intro H. 
  checkfail by fresh H exn GoalNotClosed.
Abort.

(*==================================================================*)
(* testing the `fresh` tactic *)

name nA : index -> message.
name nB : index * index -> message.
name nD : message.

op pA : index -> bool.
op pB : index -> index -> bool.
op pD : bool.

let fn @system:P u with
| A i     when happens(u) -> if pA i then nA i
| B (i,j) when happens(u)  -> if pB i j then nB (i,j)
| D       when happens(u)  -> if pD then nD
| init    -> empty
| _ when not (happens u) -> empty.
Proof.
have H :
(forall (i:index),
   happens (A(i)) =>
   (forall (i0,j:index), B(i0, j) <> A(i) || not (happens (A(i)))) &&
   (D <> A(i) || not (happens (A(i)))) &&
   (init <> A(i)) &&
   forall (x:timestamp), x <> A(i) || happens (A(i))) &&
(forall (i,j:index),
   happens (B(i, j)) =>
   (forall (i0:index), A(i0) <> B(i, j) || not (happens (B(i, j)))) &&
   (D <> B(i, j) || not (happens (B(i, j)))) &&
   (init <> B(i, j)) &&
   forall (x:timestamp), x <> B(i, j) || happens (B(i, j))) &&
(happens D =>
 (forall (i,j:index), B(i, j) <> D || not (happens D)) &&
 (forall (i:index), A(i) <> D || not (happens D)) &&
 (init <> D) && forall (x:timestamp), x <> D || happens D) 
&&
((D <> init || not (happens init)) &&
 (forall (i,j:index), B(i, j) <> init || not (happens init)) &&
 (forall (i:index), A(i) <> init || not (happens init)) &&
 forall (x:timestamp), x <> init || happens init) &&
forall (x:timestamp),
  not (happens x) =>
  (init <> x) &&
  (D <> x || not (happens x)) &&
  (forall (i,j:index), B(i, j) <> x || not (happens x)) &&
  forall (i:index), A(i) <> x || not (happens x)
by simpl; auto.
assumption.
Qed.

lemma _ @system:P t : 
  ((D <= t && pD) => false) =>
  fn t = nD => false.
Proof.
  intro A H. 
  fresh H.
  assumption A.
Qed.

lemma _ @system:P t i : 
  ((A i <= t && pA i) => false) =>
  fn t = nA i => false.
Proof.
  intro A H. 
  fresh H.
  assumption A.
Qed.

lemma _ @system:P t i j : 
  ((B(i, j) <= t && pB i j) => false) =>
  fn t = nB (i, j) => false.
Proof.
  intro A H. 
  fresh H.
  assumption A.
Qed.

(*==================================================================*)
(* `x` is a dummy argument here *)
let rec has_A @system:P (x : int) t with
| A _     when happens t -> true
| B (_,_) when happens t -> has_A x (pred t)
| D       when happens t -> has_A x (pred t)
| init -> false
| _ when not (happens t) -> false.
Proof.
have Hyp: (forall (t:timestamp), D = t => happens(t) => pred t < t) &&
forall (t:timestamp,x0,x1:index), B(x0, x1) = t => happens(t) => pred t < t 
by auto.
assumption.
Qed.
Proof.
have H :
(forall (x0:index),
   happens (A(x0)) =>
   (forall (x1,x2:index), B(x1, x2) <> A(x0) || not (happens (A(x0)))) 
   &&
   (D <> A(x0) || not (happens (A(x0)))) &&
   (init <> A(x0)) &&
   forall (x1:timestamp), x1 <> A(x0) || happens (A(x0))) &&
(forall (x0,x1:index),
   happens (B(x0, x1)) =>
   (forall (x2:index), A(x2) <> B(x0, x1) || not (happens (B(x0, x1)))) 
   &&
   (D <> B(x0, x1) || not (happens (B(x0, x1)))) &&
   (init <> B(x0, x1)) &&
   forall (x2:timestamp), x2 <> B(x0, x1) || happens (B(x0, x1))) &&
(happens D =>
 (forall (x0,x1:index), B(x0, x1) <> D || not (happens D)) &&
 (forall (x0:index), A(x0) <> D || not (happens D)) &&
 (init <> D) && forall (x0:timestamp), x0 <> D || happens D) 
&&
((D <> init || not (happens init)) &&
 (forall (x0,x1:index), B(x0, x1) <> init || not (happens init)) &&
 (forall (x0:index), A(x0) <> init || not (happens init)) &&
 forall (x0:timestamp), x0 <> init || happens init) &&
forall (x0:timestamp),
  not (happens x0) =>
  (init <> x0) &&
  (D <> x0 || not (happens x0)) &&
  (forall (x1,x2:index), B(x1, x2) <> x0 || not (happens x0)) &&
  forall (x1:index), A(x1) <> x0 || not (happens x0)
by simpl; auto.
assumption.
Qed.

lemma [P] _ x t : happens t => (has_A x t <=> exists i, A i <= t).
Proof.
  induction t.
  intro t IH Hap.
  case t.
  + intro Eq.
    rewrite /has_A.
    auto.
  + intro [i Eq].
    rewrite /has_A.
    split; 2: auto.
    by intro ?; exists i.
  + intro [i j Eq].
    rewrite /has_A.
    rewrite IH Eq //. 
    have A : 
     (exists (i0:index), A(i0) <= pred (B(i, j))) <=>
      exists (i0:index), A(i0) <= B(i, j) by admit.
    assumption A.
  + intro Eq.
    rewrite /has_A.
    rewrite IH //. 
    have A : 
     (exists (i0:index), A(i0) <= pred D) <=>
      exists (i0:index), A(i0) <= D by admit.
    assumption A.
Qed.

lemma [P] _ x t : has_A x t <=> exists i, A i <= t.
Proof.
  expand ~def has_A. 
Abort.

(*------------------------------------------------------------------*)
(* `x` is a dummy argument here *)
let bar @system:P ((x,y) : int * int) t with
| A _    when happens t -> x
| B (_,_) when happens t-> y
| D       when happens t -> x
| init -> if x =  y then 24 else 42
| _ when not (happens t) -> 10.
Proof.
auto.
Qed.
lemma [P] _ i j :
happens(A i, B(i,j),D) =>
  bar (1,2) (A i    ) = 1 &&
  bar (1,2) (B (i,j)) = 2 &&
  bar (1,2) D         = 1 &&
  bar (1,2) init = 42 &&
  bar (1,1) init = 24.
Proof. auto. Qed.

(*------------------------------------------------------------------*)
let rec foo (x : int) = if x <= 0 then 0 else 1.
let rec fac (x : int) = if x <= 0 then 1 else x * fac (x - 1).
Proof.
have C : (forall (x:int), not (x <= 0) => x - 1 < x ) by admit.
assumption.
Qed.

lemma _ @set:'P : fac 5 = 120.
Proof. 
  rewrite /fac if_false //=. 
  rewrite /fac if_false //=. 
  rewrite /fac if_false //=. 
  rewrite /fac if_false //=. 
  rewrite /fac if_false //=. 
  rewrite /fac if_true //.
Qed.

lemma _ @set:'P x : x >= 0 => fac (x + 1) = (x + 1) * fac x.
Proof. 
  intro A.
  remember fac x as y => E.
  rewrite /fac !E /=. 
  have H := Int.add_assoc. 
  rewrite /assoc in H. 
  rewrite H /=.
  rewrite if_false //; 1: by have ? : x + 1 > 0 by admit.
Qed.

abstract  better_lt : int -> int -> bool.

axiom wf_better_lt @set:'P  : well_founded (better_lt).

let rec @op:better_lt fac' (x : int) = if x <= 0 then 1 else x * fac' (x - 1).
Proof.
apply wf_better_lt.
Qed.

Proof.
have C : (forall (x:int), not (x <= 0) => better_lt (x - 1)  x ) by admit.
assumption.
Qed.

let rec is_even (x:int) =
if x=0 then true else is_odd (x-1)
and
is_odd (x:int) =
if x=0 then false else is_even (x-1).
Proof.
have H : (forall (x:int), not (x = 0) => x - 1 < x) &&
forall (x:int), not (x = 0) => x - 1 < x 

by admit.
assumption.
Qed.

lemma _ @set:'P :
 is_odd 3.
Proof.
  rewrite /is_odd if_false //=.   
  rewrite /is_even if_false //=.     
  rewrite /is_odd if_false //=.   
  rewrite /is_even if_true //=.  
Qed.

(*------------------------------------------------------------------*)
let rec fac2 (x : int) with
| _ when x < 0 -> 1
| 0 -> 1
| y + 1 when x > 0 -> x * fac2 y.
Proof. 
 (* smt. *) admit. (* FIXME: smt *)
Qed.
Proof.
  split. 
  + repeat split.
    - intro x0 * /=. 
     (* smt. *) admit. (* FIXME: smt *)
    - auto. 
    - intro x.
     (* smt. *) admit. (* FIXME: smt *)
    - intro x * /=. 
     (* smt. *) admit. (* FIXME: smt *)
 + intro x /=. have ? : 
x < 0 || 0 = x || exists (y:int), y + 1 = x && x > 0  by admit.
   case H.
   - by left. 
   - right; left; auto.
   - right; right; auto.
Qed.

lemma _ @set:'P : fac2 5 = 120.
Proof.
  expand ~def fac2 => /=. 
  expand ~def fac2 => /=. 
  expand ~def fac2 => /=. 
  expand ~def fac2 => /=. 

  expand ~def fac2 => /=.
  expand ~def fac2 => /=. 
  auto.  
Qed.

let rec broken_fac2 (x : int) with
| _ when x < 0 -> 1
| 0 -> 1
| x + 1 when x > 0 -> (x + 1) * broken_fac2 x. (* this definition is wrong, we recaptured the x. *)
Proof. 
admit.
Qed.
Proof.
split. admit.

have H : forall (x:int), x < 0 || 0 = x || exists (x0:int), x0 + 1 = x && x0 > 0 by admit.
  (* impossible formula to prove, we are missing the case x=1, as expected *)
assumption.

Qed.

lemma _ @set:'P x : x + 1 > 0 => fac2 (x + 1) = (x + 1) * fac2 x.
Proof.
  intro H.
  set a := fac2 x.
  expand ~def fac2 => /=. 
  simpl ~delta.
  by rewrite if_true.
Qed.


(* Not exhaustive checks *)

let ne_test (x : bool) with
(* | true  -> 1 *)
| false -> 0.
Proof.
have H : forall (x:bool), false = x  by admit. (* of course false admit *)
assumption.
Qed.

let ne_test2 (x : bool * bool) with
(* | (true , _) -> 1 *)
| (false, false) -> 0
| (false, true ) -> 2.
Proof.
split. 
have H : 
  ((false, true) <> (false, false)) &&
  ((false, false) <> (false, true)).
{ auto. }
assumption.

have H : forall (x:bool * bool), (false, false) = x || (false, true) = x  by admit.
assumption.
Qed.

let ne_test3 (x : bool * bool) with
| (true , _) -> 1
(* | (false, false) -> 0 *)
| (false, true ) -> 2.
Proof.
split.
have H : 
(forall (x0:bool), (false, true) <> (true, x0)) &&
forall (x0:bool), (true, x0) <> (false, true) .
{ auto. }
assumption.

have H : forall (x:bool * bool),
  (exists (x0:bool), (true, x0) = x) || (false, true) = x by admit.
assumption.
Qed.

op prop : bool.

  (* missing [A _] because of [prop] *)
let f0 @system:P (x : int) u with
| A i     when happens (A i) && prop -> 0
| init                               -> 1
| _       when not (happens u)       -> 2.
Proof.
split.
auto.

have H : forall (u:timestamp),
  (exists (i:index), A(i) = u && happens(A(i)) && prop) ||
  init = u || not(happens(u)) by admit.
assumption.
Qed.

  (* missing [init] *)
let f1 @system:P (x : int) u with
| A i     when happens (A i)     -> 0
| _       when not (happens u)   -> 2.
Proof.
split.
admit.

have H : forall (u:timestamp),
  (exists (i:index), A(i) = u && happens(A(i))) ||
  not(happens(u))
 by admit.
assumption.
Qed.
