(*******************************************************************************
OSK - LFMTP - part 2 - strong secrecy of outputs
*******************************************************************************)

hash h1
hash h2

name key : message
name key': message
name seed : message


mutable kT : message = seed

channel cT 
channel cO

process tag(j:index) =
  new nT;
  kT := h1(kT,key);
  out(cT, diff(h2(kT,key'),nT)).

system (!_j T: tag(j) | !_j O: in(cO,x);out(cO,<h1(x,key),h2(x,key')>))


(* AXIOM *)

axiom restr : forall (j1,j2:index), j1 <> j2 => input@O(j1)  <> input@O(j2).
axiom never_repeat: forall (t:timestamp), forall (i:index), t < T(i)  => kT@t <> kT@T(i).



equiv strongSecrecy.

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
admit. (* apply previous result *)
project.
use never_repeat with T(j0), j.
fresh 1.
yesif 1.


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
project.
admit. (* apply previous result *)
fresh 2.
prf 1.

yesif 1.
split.
use restr with j0, j.
admit. (* apply previous result *)
fresh 1.
Qed.


