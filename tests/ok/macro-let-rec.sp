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
| _ when x > 0 -> x * fac2 (x - 1).
Proof. 
 smt. 
Qed.
Proof. smt. Qed.

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

lemma _ @set:'P x : x + 1 > 0 => fac2 (x + 1) = (x + 1) * fac2 x.
Proof.
  intro H.
  set a := fac2 x.
  expand ~def fac2 => /=. 
  have -> : (x + 1) - 1 = x by smt.
  simpl ~delta.
  rewrite if_true //.
Qed.

let rec broken_fac2 (x : int) with
| _ when x < 0 -> 1
| 0 -> 1
| x when x - 1 > 0 -> x * broken_fac2 (x - 1).
(* this definition is wrong, we recaptured the x. *)
Proof. 
admit.
Qed.
Proof.
admit.
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
| _       when not (happens u) && x=0 -> 2
| _       when not (happens u) && x=1 -> 3.
Proof.

have H : forall (u:timestamp,x:int),
  (exists (i:index), A(i) = u && happens(A(i)) && prop) ||
  init = u || (not(happens(u)) && x = 0) || not(happens(u)) && x = 1 by admit.
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


let rec plus (x : int) (y:int) with
| 0 -> y
| _ when y= 0 ->  x
| 1 -> y + 1
| _ when y=1 -> 1 + x
| 0 -> 1
| _ when y > 1 && x>1 -> 1+ (plus (x) (y-1)).
Proof.
have H : forall (x,y:int), y > 1 && x > 1 => (y - 1) < y by admit.
assumption.
Qed.
