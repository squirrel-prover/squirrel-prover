(*******************************************************************************
TOY EXAMPLE WITH STATE

WA and ND goals with a toy protocol (specific reader).
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

axiom stateInit :
  forall (i:index), kT(i)@init = seed(i) && kR(i)@init = hState(seed(i),keyState(i))

(* i = tag's identity, j = tag's session for identity i *)
process tag(i:index,j:index) =
  kT(i) := hState(kT(i),keyState(i));
  out(cT, hMsg(kT(i),keyMsg(i)))

(* k = entry k in the database (ie for a given tag's identity), kk = reader's session for entry k *)
process reader(k:index,kk:index) =
  in(cT,x);
  if x = hMsg(kR(k),keyMsg(k)) then
    kR(k) := hState(kR(k),keyState(k));
    out(cR,ok)
  else
    out(cR,ko)

system ((!_k !_kk R: reader(k,kk)) | (!_i !_j T: tag(i,j))).

goal wa_R :
forall (k,kk:index),
  cond@R(k,kk) =>
  (exists (j:index), T(k,j) < R(k,kk) && output@T(k,j) = input@R(k,kk)).
Proof.
intros.
expand cond@R(k,kk).
euf M0.
exists j.
case H0.
Qed.

(* avec reader spécifique, on peut imaginer écrire une sorte de condition ND comme celle-ci *)
(* mais pour que ce soit correct il faudrait arriver à exprimer que T(i,j) et T(i,j') sont 2 actions
consécutives du tag d'identité i, ce qui ne correspond pas à T(i,j)=pred(T(i,j')) car le reader peut
avoir joué entre temps, et idem pour R(k,kk)/R(k,kk') *)
goal nd_R :
forall (i,j,k,kk:index),
  (T(i,j) < R(k,kk) && output@T(i,j) = input@R(k,kk) && cond@R(k,kk)) =>
    (forall (j',kk':index), 
     T(i,j) < T(i,j') && R(k,kk) < R(k,kk') && output@T(i,j') = input@R(k,kk') => cond@R(k,kk')).
Proof.
admit.
Qed.
