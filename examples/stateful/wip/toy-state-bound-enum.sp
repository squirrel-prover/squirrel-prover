(*******************************************************************************
TOY EXAMPLE WITH STATE

Authentication goals with a toy protocol (bounded, generic reader).

In this model, the database lookup performed by the reader is explicitly
enumerated (3 possible values, ie a desynchronisation of at most 3 sessions).
*******************************************************************************)

hash hMsg
hash hState

abstract ok : message
abstract ko : message
abstract testOk : message

name seed : index->message
name keyState : index->message
name keyMsg : index->message

mutable kT(i:index) : message = seed(i)
mutable kR(ii:index) : message = seed(ii)

channel cT
channel cR

(* i = tag's identity, j = tag's session for identity i *)
process tag(i:index,j:index) =
  kT(i) := hState(kT(i),keyState(i));
  out(cT, hMsg(kT(i),keyMsg(i)))

(* k = generic reader's session *)
process reader(k:index) =
  in(cR,x);
  try find i such that x = hMsg(kR(i),keyMsg(i)) in
    kR(i):= hState(kR(i),keyState(i));
    out(cR,ok)
  else
    try find i such that  x=hMsg(hState(kR(i),keyState(i)),keyMsg(i)) in
      kR(i):= hState(hState(kR(i),keyState(i)),keyState(i));
      out(cR,ok)
    else
      try find i such that  x=hMsg(hState(hState(kR(i),keyState(i)),keyState(i)),keyMsg(i)) in
        kR(i):= hState(hState(hState(kR(i),keyState(i)),keyState(i)),keyState(i));
        out(cR,ok)
      else
        out(cR,ko)


system ((!_k R: reader(k)) | (!_i !_j T: tag(i,j))).

goal wa_R0 :
forall (k:index,i:index),
  happens(R(k,i)) =>
  (cond@R(k,i) =>
    (exists (j:index), T(i,j) < R(k,i) && output@T(i,j) = input@R(k,i))).
Proof.
intro *.
expand cond@R(k,i).
euf H.
by exists j.
Qed.

goal wa_R1 :
forall (k:index,i:index),
  happens(R1(k,i)) =>
  (cond@R1(k,i) =>
    (exists (j:index), T(i,j) < R1(k,i) && output@T(i,j) = input@R1(k,i))).
Proof.
intro *.
expand cond@R1(k,i).
euf Meq.
by exists j.
Qed.

goal wa_R2 :
forall (k:index,i:index),
  happens(R2(k,i)) =>
  (cond@R2(k,i) =>
    (exists (j:index), T(i,j) < R2(k,i) && output@T(i,j) = input@R2(k,i))).
Proof.
intro *.
expand cond@R2(k,i).
euf Meq.
by exists j.
Qed.
