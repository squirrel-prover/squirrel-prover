hash h

abstract ok:message
abstract error:message

axiom pair : forall (x:message) <fst(x), snd(x)> = x

name key : index->message

channel cT
channel cR

process tag(i:index) =
  new nT;
  out(cT, <nT, h(nT,key(i))>)

process reader(j:index) =
  in(cT,x);
  try find i such that snd(x) = h(fst(x),key(i)) in
    out(cR,ok)
  else
    out(cR,error)

system ((!_j R: reader(j)) | (!_i !_k T: tag(i))).

goal wa :
  forall (i:index, j:index),
  cond@R(j,i) => 
  exists (k:index), (
  T(i,k) <= R(j,i) &&
  input@R(j,i) = output@T(i,k)).

Proof.
 simpl.
 expand cond@R(j,i).
 euf M0.
 exists k.
 apply pair to input@R(j,i).
Qed.
