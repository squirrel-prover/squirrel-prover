(*******************************************************************************
TOY EXAMPLE WITH STATE

Successive hashes for state values are replaced by fresh names.
Magic protocol because these fresh names must be shared between tag and reader.
*******************************************************************************)

hash hMsg

abstract ok : message
abstract ko : message

name seed : index->message
name keyMsg : index->index->message

channel cT
channel cR

(* i = tag's identity, j = tag's session for identity i *)
process tag(i:index,j:index) =
  out(cT, hMsg(seed(i),keyMsg(i,j)))

(* k = entry k in the database (ie for a given tag's identity), 
   kk = reader's session for entry k *)
process reader(k:index,kk:index) =
  in(cT,x);
  if x = hMsg(seed(k),keyMsg(k,kk)) then
    out(cR,ok)
  else
    out(cR,ko)

system ((!_k !_kk R: reader(k,kk)) | (!_i !_j T: tag(i,j))).

goal wa_R :
(* (i,j)=(k,kk) is necessary to have keyMsg(i,j)=keyMsg(k,kk) *)
forall (k,kk:index),
  happens(R(k,kk)) => 
  (cond@R(k,kk) =>
    exists (i,j:index), 
      T(i,j) < R(k,kk) && output@T(i,j) = input@R(k,kk) && i=k && j=kk).
Proof.
intro *.
expand cond@R(k,kk).
project.
(* LEFT *)
euf H.
exists k,kk.
(* RIGHT *)
euf H.
exists k,kk.
Qed.
