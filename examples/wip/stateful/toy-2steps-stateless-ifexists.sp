(*******************************************************************************
TOY EXAMPLE WITH STATE

The goal is to prove the equivalence of these 2 systems:

LEFT SYSTEM
T -> R : h(n(i,j),key(i))
R -> T : ok

RIGHT SYSTEM
T -> R : nIdeal(i,j)
R -> T : ok

Remarks:
-  n(i,j) and nIdeal(i,j) are "magic" nonces, since they are shared between the
tag and the reader.
- The reader conditional is modelled with a if exists.

Current state of the proof:
- The fresh tactic (used for the right system) seems not enough to conclude in
the same way as euf (used for the left system) because the fresh tactic takes
into account occurrences in conditions (this is not the case for euf).
*******************************************************************************)

hash h

abstract ok : message
abstract ko : message

name seed : index->message
name key : index->message
name n : index->index->message
name nIdeal : index->index->message

channel cT
channel cR

process tag(i:index,j:index) =
  out(cT, diff(h(n(i,j),key(i)),nIdeal(i,j)))

process reader(k:index) =
  in(cT,x);
  if exists (ii,jj:index), x = diff(h(n(ii,jj),key(ii)), nIdeal(ii,jj)) then
    out(cR,ok)
  else
    out(cR,ko)

system ((!_k R: reader(k)) | (!_i !_j T: tag(i,j))).

equiv real_ideal.
Proof.
induction t.

(* CASE R(k) *)
expand frame@R(k).
fa 0.
fa 1.
expand output@R(k).
expand exec@R(k).
equivalent
  cond@R(k),
  exists (i,j:index), T(i,j) < R(k) && output@T(i,j) = input@R(k).
split.
(* cond => honest *)
expand cond@R(k).
project.
(* LEFT *)
euf Meq.
exists ii,j.
(* RIGHT *)
fresh Meq. 
case H0.
by exists ii,jj. 
admit. (* ??? *)
admit. (* ??? *)

(* honest => cond *)
expand cond@R(k).
by exists i,j.
by fadup 1.

(* CASE R1(k) *)
expand frame@R1(k).
fa 0.
fa 1.
expand output@R1(k).
expand exec@R1(k).
equivalent
  cond@R1(k),
  not (exists (i,j:index), T(i,j) < R1(k) && output@T(i,j) = input@R1(k)).
split.
(* not(honest) => not(cond) *)
expand cond@R1(k).
notleft H0.
use H0 with i,j.
(* not(cond) => not(honest) *)
expand cond@R1(k).
notleft H0.
project.
(* LEFT *)
euf Meq.
use H0 with ii,j.
case H1.
(* RIGHT *)
fresh Meq. 
case H1.
by use H0 with ii,jj; case H1.
admit.
admit.
fadup 1.

(* CASE T(i,j) *)
expandall.
fa 0; fa 1; fa 1.
prf 1.
yesif 1.
project.
split.
admit. (* ??? *)
admit. (* ??? *)
fresh 1.
yesif 1.
admit. (* ??? *)
Qed.
