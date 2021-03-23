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
- The reader conditional is modelled with a try find.

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
  try find ii,jj such that x = diff(h(n(ii,jj),key(ii)), nIdeal(ii,jj)) in
    out(cR,ok)
  else
    out(cR,ko)

system ((!_k R: reader(k)) | (!_i !_j T: tag(i,j))).

equiv real_ideal.
Proof.
induction t.

(* CASE R(k,ii,jj) *)
expand frame@R(k,ii,jj).
fa 0.
fa 1.
expand output@R(k,ii,jj).
equivalent
  exec@R(k,ii,jj),
  exec@pred(R(k,ii,jj)) && (T(ii,jj) < R(k,ii,jj) && output@T(ii,jj) = input@R(k,ii,jj)).
split.
(* cond => honest *)
expand exec@R(k,ii,jj).
expand cond@R(k,ii,jj).
project.
(* LEFT *)
euf H1.
(* RIGHT *)
fresh H1. 
case H2.
admit. (* ??? *)
admit. (* need induction? *)
(* honest => cond *)
expand exec@R(k,ii,jj).
expand cond@R(k,ii,jj).
fadup 1.

(* CASE R1(k) *)
admit.

(* CASE T(i,j) *)
expandall.
fa 0. fa 1. fa 1.
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
