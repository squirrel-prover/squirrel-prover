(*******************************************************************************
TOY EXAMPLE WITH STATE
*******************************************************************************)

hash hMsg
hash hState

abstract seed : message
abstract ok : message
abstract ko : message

name keyMsg : message
name keyState : message

mutable kT : index->message
mutable kR : index->message

channel cT
channel cR

axiom stateInit :
  forall (i:index), kT(i)@init = seed && kR(i)@init = hState(seed,keyState)

(* i = tag's identity, j = tag's session for identity i *)
process tag(i:index,j:index) =
  (* pas réussi à prouver stateUpdate si j'utilise une macro pour
  faire output avec la valeur avant update *)
  kT(i) := hState(kT(i),keyState);
  out(cT, hMsg(kT(i),keyMsg))

(* k = entry k in the database (ie for a given tag's identity), kk = reader's session for entry k *)
process reader(k:index,kk:index) =
  in(cT,x);
  if x = hMsg(kR(k),keyMsg) then
    kR(k) := hState(kR(k),keyState);
    out(cR,ok)
  else
    out(cR,ko)

system ((!_k !_kk R: reader(k,kk)) | (!_i !_j T: tag(i,j))).

goal stateUpdate :
forall (t:timestamp), (forall (i,j:index), t=T(i,j) => kT(i)@t = hState(kT(i)@pred(t),keyState)).
Proof.
induction.
Qed.

goal stateIncrease :
forall (t:timestamp), (forall (i,j:index), t=T(i,j) => kT(i)@t <> kT(i)@pred(t)).
Proof.
induction.
assert kT(i)@pred(T(i,j))=hState(kT(i)@pred(T(i,j)),keyState).
(* pour raisonner sur M3 il nous faudrait une variante de fresh ?*) admit.
Qed.

goal wa_R :
forall (k,kk:index),
  cond@R(k,kk) =>
  (exists (i,j:index), T(i,j) < R(k,kk) && output@T(i,j) = input@R(k,kk)).
Proof.
intros.
expand cond@R(k,kk).
project.
(* LEFT *)
euf M0.
exists i, j.
case H0.
(* RIGHT *)
euf M0.
exists i,j.
case H0.
Qed.

(* avec reader spécifique, on peut imaginer écrire une sorte de condition ND comme celle-ci *)
(* mais ici elle est fausse car le test côté reader n'autorise pas le tag à avoir joué plusieurs
sessions entre temps *)
goal nd_R :
forall (i,j,k,kk:index),
  (T(i,j) < R(k,kk) && output@T(i,j) = input@R(k,kk) && cond@R(k,kk)) =>
    (forall (j',kk':index), 
      T(i,j) = pred(T(i,j')) && R(k,kk) < R(k,kk') && output@T(i,j') = input@R(k,kk') => cond@R(k,kk')).
Proof.
intros.
expand cond@R(k,kk). expand cond@R(k,kk').
assert input@R(k,kk') = hMsg(hState(kT(i)@T(i,j),keyState),keyMsg).
(* à continuer *) admit.
Qed.
