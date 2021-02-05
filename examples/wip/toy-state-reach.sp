(*******************************************************************************
TOY EXAMPLE WITH STATE

         kT := hState(kT,keyState)
T -> R : hMsg(kT,keyMsg)
         
         kR := hState(kR,keyState)   if x = hMsg(kR,keyMsg)
R -> T : ok

PROOFS
- authentication
*******************************************************************************)

hash hMsg
hash hState

abstract ok : message
abstract ko : message

name seed : index->message
name keyMsg : index->message
name keyState : index->message

mutable kT : index->message
mutable kR : index->message

channel cT
channel cR

(* i = tag's identity, j = tag's session for identity i *)
process tag(i:index,j:index) =
  kT(i) := hState(kT(i),keyState(i));
  out(cT, hMsg(kT(i),keyMsg(i)))

(* k = reader's session *)
process reader(k:index) =
  in(cT,x);
  try find ii such that x = hMsg(kR(ii),keyMsg(ii)) in
    kR(ii) := hState(kR(ii),keyState(ii));
    out(cR,ok)
  else
    out(cR,ko)

system ((!_k R: reader(k)) | (!_i !_j T: tag(i,j))).

goal wa_R :
forall (k,ii:index),
  cond@R(k,ii) =>
  (exists (j:index), T(ii,j) < R(k,ii) && output@T(ii,j) = input@R(k,ii)).
Proof.
intros.
expand cond@R(k,ii).
euf M0.
exists j.
Qed.
