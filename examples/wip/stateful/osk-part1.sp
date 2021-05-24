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


(* kT@t = kT@t' where t' is init or the previous update of kT *)
goal lastUpdate : forall (t:timestamp) 
  happens(t) =>
  ((kT@t = kT@init && forall (ii:index), happens(T(ii)) => t < T(ii)) ||
    (exists j:index,
     kT@t = kT@T(j) &&
     T(j) <= t &&
     (forall (j':index), happens(T(j')) => (T(j')<=T(j) || t<T(j'))))).
Proof.
induction.
case t.

(* 1/4  t = init *)
subst t, init.
by left.

(* 2/4 t = T(j) - interesting case *)
subst t, T(j).
use H with pred(T(j)) as H1.
case H1.
right.
by exists j.
right.
by exists j.

(* 3/4 t =T1(j) *)
subst t, T1(j).
use H with pred(T1(j)) as H1.
case H1.
left.
by use H0 with ii.
right.
exists j0.
use H1 with j'.
case H0.

(* 4/4 t=O(j) *)
subst t, O(j).
use H with pred(O(j)) as H1.
case H1.
left.
by use H0 with ii.
right.
exists j0.
use H1 with j'.
case H0.

Qed.



goal stateInequality :
  forall (t:timestamp),
  (forall (t':timestamp), forall (i:index)
     happens(t) =>
     (t = T(i) && t' < t => kT@t <> kT@t')).

Proof.
induction.
subst t, T(i).
assert kT@t' = h1(kT@pred(T(i)),key).
euf Meq0.

(* first case *)
assert T(j) < T(i).
case H0.



use lastUpdate with pred(T(i)) as HLasti.
case HLasti.
use H1 with j.


use lastUpdate with pred(T(j)) as HLastj.
case HLastj.
use H with T(j0), init, j0.


assert T(j1) = T(j0) || T(j0) < T(j1) || T(j1) < T(j0).
case H1.

(* T(j1) = T(j0) *)
admit.

(* T(j0) < T(j1) *)
use H with T(j1), T(j0),  j1.

(* T(j1) < T(j0) *)
use H with T(j0), T(j1), j0.


(* second case *)

assert O(j) < T(i).
case H0.


use lastUpdate with pred(T(i)) as HLasti.
case HLasti.
admit.

use H2 with 
use H with T(j0), t', j0.

use H1 with j.

admit.
Qed.


use lastUpdate with pred(T(j)) as HLastj.
case HLastj.

(* T(j) < T(i)
   kT@pred(T(j)) = kT@pred(T(i))
   in order to use H we need a timestamp of the form T() but pred() has no reason to be of that form ... 
   this is where lastUpdate comes into play *)


use lastUpdate with pred(T(i)) as HLasti.
case HLasti.
use H1 with j.





use lastUpdate with pred(T(j)) as HLastj.
case HLastj.




use H with T(j0), init,j0.


use lastUpdate with pred(T(i)) as HLasti.
case HLasti.
use H2 with j.
use H with T(j0), init,j0.


admit.

case H0.
admit.


use lastUpdate with pred(T(i)) as HLasti.
case HLasti.

admit.
use H2 with i.
use H with T(j0), T(i), j0.


use H1 with j.
use H with T(j0), init,j0.

assert T(j0) < T(j1) || T(j1) < T(j0) || T(j1) = T(j0).
case H1.
admit.
admit.
subst j0, j1.

nosimpl(use H with T(j1), pred(T(j)),j1 as H4).

use lastUpdate with pred(T(i)) as HLasti.
case HLastj.
case HLasti.
admit.
admit.

case HLasti.
admit.

use H with T(j0),T(j1),j0.
use H2 with j1.
case H1.
assert (T(j1) < T(j0) || T(j1) = T(j0)).
admit.

use H with T(j)), init, j.

simpl.



(* kT@pred(T(i)) = kT@init this can actually happen only 
if tag has not played from init to pred(T(i))
   but we know that T(j) < T(i): absurd *)
use H with T(j), init, j.

Qed.

goal lemma_never_repeat: forall (t:timestamp), forall (i:index), t < T(i)  => kT@t <> kT@T(i).
Proof.
intro *.



equiv monfoo (t:timestamp,i:index) : 
  [happens(t,T(i))] -> frame@t, seq(i -> if (T(i)< t) then diff(kT@T(i),freshnonce(i))).


Proof.
induction t.

(* init *)
intro *.
(* admit. (* HELP !! easy mais je ne sais pas quoi dire *) *)
nosimpl(rewrite if_false). (* note: if_false est un lemme plus haut. *)
nosimpl(byequiv).
simpl.
simpl.
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
nosimpl(yesif 1).
nosimpl(split).
admit.
simpl.
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
nosimpl(yesif 2).
nosimpl(split).
rewrite if_false.

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
