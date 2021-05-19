(*******************************************************************************
OSK - LFMTP - part 1 - secrecy of states
*******************************************************************************)

hash h1
hash h2

name key : message
name key': message
name seed : message
name n : message
name freshnonce: index -> message


mutable kT : message = seed

channel cT 
channel cO
channel cS

process tag(j:index) =
  kT := h1(kT,key);
  out(cT, h2(kT,key'));out(cS,diff(kT,n)).

system (!_j T: tag(j) | !_j O: in(cO,x);out(cO,<h1(x,key),h2(x,key')>)).

(* LIBRARIES *)
(* A inclure dans une lib standard *)

set autoIntro=false.

goal if_false  (b : boolean, x,y : message):
 (not b) => if b then x else y = y.
Proof.
 by intro *; noif. 
Qed.

goal if_true (b : boolean, x,y : message):
 b => if b then x else y = x.
Proof.
  by intro *; yesif.
Qed.

set autoIntro=true.

(* AXIOM *)

axiom restr : forall (j1,j2:index), j1 <> j2 => input@O(j1)  <> input@O(j2).
axiom never_repeat: forall (t:timestamp), forall (i:index), t < T(i)  => kT@t <> kT@T(i).

equiv monfoo (t:timestamp,i:index) : 
  [happens(t,T(i))] -> frame@t, seq(i -> if (T(i)< t) then diff(kT@T(i),freshnonce(i))).


Proof.
induction t.

(* init *)
intro *.
(* admit. (* HELP !! easy mais je ne sais pas quoi dire *) *)
rewrite if_false. (* note: if_false est un lemme plus haut. *)
by byequiv.

(* t = T(j) *)
intro *.
expand frame@T(j). expand exec@T(j).
expand cond@T(j). expand output@T(j).
fa 0.
fa 1.
fa 1.
prf 1.
rewrite if_true in 1.
byequiv.
admit.
(* help. (* HELP !! completement perdue je voulais faire yesif - en particulier _i78 me semble louche *) *)
admit.
admit.
admit.
Qed.

equiv foo (t: timestamp) : [happens(t)] -> frame@pred(t) -> frame@t.
Proof.
induction t.

(* t = init *)
intro *.

(* t = T(j) *)
intro *.
expand frame@T(j). expand exec@T(j).
expand cond@T(j). expand output@T(j).
fa 0.
fa 1.
fa 1.
expand kT@T(j).
prf 1.
yesif 1.
split.
assert(h1(kT@pred(T(j)),key)  = n).
admit.
fresh Meq0.
admit.
use never_repeat with T(j0), j.
fresh 1.


(* T1(j) *)
intro *.
expand frame@T1(j). expand exec@T1(j).
expand cond@T1(j). expand output@T1(j).
fa 0.
fa 1.
fa 1.
expand kT@T1(j).
admit.

(* O(j) *)
intro *.
expand frame@O(j). expand exec@O(j).
expand cond@O(j). expand output@O(j).
fa 0.
fa 1.
fa 1.
fa 1.
prf 2.
yesif 2.
split.
use restr with j0, j.
admit.
fresh 2.
prf 1.

yesif 1.
split.
use restr with j0, j.
admit.
fresh 1.
Qed.





(* kT(i)@t = kT(i)@t' where t' is init or the previous update of kT(i) *)
goal lastUpdate : forall (t:timestamp) 
  happens(t) =>
  (kT@t = kT@init  ||
    (exists j:index,
     kT@t = kT@T(j) &&
     T(j) <= t &&
     (forall (j':index), happens(T(j')) => (T(j')<=T(j) || t<T(j'))))).
Proof.
admit.
Qed.
