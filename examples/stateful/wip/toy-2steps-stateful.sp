(*******************************************************************************
TOY EXAMPLE WITH STATE

The goal is to prove the equivalence of these 2 systems:

LEFT SYSTEM
T -> R : h(kT(i),key(i))
R -> T : ok

RIGHT SYSTEM
T -> R : h(nIdeal(i,j),key(i))
R -> T : ok

Remarks:
-  nIdeal(i,j) is a "magic" nonce, since it is shared between the tag and the
reader.
- The reader conditional is modelled with a try find because we need the index
ii to know which line we need to update in the database.

Current state of the proof:
- The direction honest => cond seems incorrect to me in the way it is handled
here, I think we might need to express something more "imprecise" as what we did
with examples/wip.sp. But we cannot model the reader's conditional with
"if exists ...".

WARNING
- Actually, this equivalence cannot hold because a tag and a reader can be
desynchronised in the left system, while it cannot happen in the right system.
=> PROOF NOT UPDATED WITH NEW TRACE MODEL
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

mutable kT(i:index) : message = seed(i)
mutable kR(ii:index) : message = seed(ii)

process tag(i:index,j:index) =
  kT(i) := h(diff(kT(i),nIdeal(i,j)),key(i));
  out(cT, kT(i))

process reader(k:index) =
  in(cT,x);
  try find ii,jj such that x = h(diff(kR(ii),nIdeal(ii,jj)),key(ii)) in
    kR(ii) := diff(h(kR(ii),key(ii)), h(nIdeal(ii,jj),key(ii)));
    out(cR,ok)
  else
    out(cR,ko)

system ((!_k R: reader(k)) | (!_i !_j T: tag(i,j))).

goal [left] stateInequalityTag :
forall (i,j,j':index)
  T(i,j) < T(i,j') => kT(i)@T(i,j) <> kT(i)@T(i,j').
Proof.
admit.
Qed.

goal [left] stateInequalityReader :
forall (k,k',ii,jj,jj':index)
  R(k,ii,jj) < R(k',ii,jj') => kR(ii)@R(k,ii,jj) <> kR(ii)@R(k',ii,jj').
Proof.
admit.
Qed.

goal [right] readerPlaysAfterTag :
forall (t:timestamp),
forall (ii,jj,k:index),
  t = R(k,ii,jj) && exec@T(ii,jj) && R(k,ii,jj) < T(ii,jj) => False.
Proof.
induction.
executable T(ii,jj).
use H1 with R(k,ii,jj).
expand exec@R(k,ii,jj). expand cond@R(k,ii,jj).
euf H3.
use H with R(k1,ii,jj).
use H4 with ii,jj,k1.
Qed.

equiv real_ideal.
Proof.
induction t.

(* CASE R(k,ii,jj) *)
expand frame@R(k,ii,jj).
fa 0.
fa 1.
expand output@R(k,ii,jj).
expand exec@R(k,ii,jj).
equivalent
  cond@R(k,ii,jj),
  exists (j:index), T(ii,j) < R(k,ii,jj) && output@T(ii,j) = input@R(k,ii,jj).
split. 
(* cond => honest *)
project.
(* LEFT *)
expand cond@R(k,ii,jj).
euf H.
use stateInequalityReader with k1,k,ii,jj1,jj.
by exists j.
(* RIGHT *)
expand cond@R(k,ii,jj).
euf H.
admit. (* need induction? *)
by exists j.
(* honest => cond *)
expand cond@R(k,ii,jj).
project.
(* LEFT *)
admit. (* ??? *)
(* RIGHT *)
admit. (* ??? *)
by fadup 1.

(* CASE R1(k) *)
admit.

(* CASE T(i,j) *)
expandall.
fa 0; fa 1.
prf 1.
ifcond 1,exec@pred(T(i,j)).
fa 1.
yesif 1.
project.
split.
admit. (* reasonning on states? *)
split;1: by use stateInequalityTag with i,j1,j.
(* Adrien: tactics below did not use before my changes. *)
use readerPlaysAfterTag with R(k,ii,jj).
use H1 with ii,jj,k.
expand exec@T(ii,jj).
expand cond@T(ii,jj).

fresh 1.
Qed.
