(*******************************************************************************
SLK06

T. van Deursen and S. Radomirović, ‘Attacks on RFID Protocols’,
Cryptology ePrint Archive, vol. 2008, no. 310, pp. 1–56, Aug. 2009.

The protocol assumes that the reader and tag share the secrets k, ID, and PIN.
While ID and PIN are unique to each tag, k is equal for all tags the reader is
allowed to authenticate.
The tag further stores the timestamp TSlast of the last successful mutual
authentication initialized to 0 at the factory.

R -> T : <h(k,TS),TS>
T -> R : h(ID)               if TS > TSlast
         ID := h(ID,PIN,TS)
         TSlast := TS
R -> T : h(ID,PIN)
         ID' := h(ID,PIN,TS)
*******************************************************************************)

(*******************************************************************************
In this model, we add parallel processes to the global system to model the fact
that the attacker can hash messages.
In order to prove the authentication goals, we have to prove that an input
cannot be equal to some values, ie that values stored in states are not
deducible.
The corresponding goals secretStateTag and secretStateReader are not yet fully
proven:
  - admit. (* ok *) ==> I think it is possible to conclude using reasonings on
state values, but it is to be confirmed.
  - admit. (* TODO *) ==> I have not yet managed to conclude, and/or have not
really any idea how to proceed.
*******************************************************************************)

abstract ok : message
abstract error : message

abstract TSinit : message
abstract TSorderOk : message
abstract TSorder : message->message->message
abstract TSnext : message->message

name k : message
name key1 : message
name key2 : message
name key3 : message

hash h
hash h1
hash h2
hash h3

name idinit : index->message
name pin : index->message

mutable kT : index->message (* <ID,TSlast> *)
mutable kR : index->message (* <ID> *)
mutable TS : message

channel cT
channel cR
channel c

(* i = tag's identity, j = tag's session for identity i *)
process tag(i:index,j:index) =
  in(cR, x1);
  if fst(x1) = h(snd(x1),k) && TSorder(snd(kT(i)),snd(x1)) = TSorderOk then
    out(cT, h1(fst(kT(i)),key1));
    in(cR, x3);
    if x3 = h2(<fst(kT(i)),pin(i)>,key2) then
      kT(i) := <h3(<<fst(kT(i)),pin(i)>,snd(x1)>,key3), snd(x1)>;
      out(cT, ok)
    else
      out(cT, error)
  else
    out(cT, error)

(* jj = generic reader's session *)
process reader(jj:index) =
  TS := TSnext(TS);
  out(cR, <h(TS,k),TS>);
  in(cT, x2);
  try find ii such that x2 = h1(kR(ii), key1) in
    let m = h2(<kR(ii),pin(ii)>,key2) in
    kR(ii) := h3(<<kR(ii),pin(ii)>,TS>,key3);
    out(cR, m)
  else
    out(cR, error)

system ((!_jj R: reader(jj)) | (!_i !_j T: tag(i,j))
        | !_kk (in(c,m); out(c,h1(m,key1)))
        | !_kk (in(c,m); out(c,h2(m,key2)))
        | !_kk (in(c,m); out(c,h3(m,key3)))).

(* /!\ incorrect modelling of state initial values *)
axiom stateTagInit : forall (i:index), kT(i)@init = <idinit(i),TSinit>
axiom stateReaderInit : forall (ii:index), kR(ii)@init = idinit(ii).

goal lastUpdateTag_ :
forall (t:timestamp), forall (i:index),
  (kT(i)@t = kT(i)@init && forall (j':index) t < T1(i,j')) ||
  (exists j:index,
    kT(i)@t = kT(i)@T1(i,j) &&
    T1(i,j) <= t &&
    (forall (j':index), T1(i,j')<=T1(i,j) || t<T1(i,j'))).
Proof.
induction.
nosimpl(revert H => IH0).
case t. 

substitute t,init.
left.

substitute t,R(jj).
have H := IH0 to pred(R(jj)).
have P := H to i; case P.
by left; apply H0 to j'.
right; exists j; apply H1 to j'. 
by case H0.

substitute t,R1(jj,ii).
have H := IH0 to pred(R1(jj,ii)).
have P := H to i; case P.
by left; apply H0 to j'.
right; exists j; apply H1 to j'.
by case H0.

substitute t,R2(jj).
have H := IH0 to pred(R2(jj)).
have P := H to i; case P.
by left; apply H0 to j'.
right; exists j; apply H1 to j'.
by case H0.

substitute t,T(i1,j).
have H := IH0 to pred(T(i1,j)).
have P := H to i; case P.
by left; apply H0 to j'.
right; exists j1; apply H1 to j'.
by case H0.

substitute t,T1(i1,j).
have H := IH0 to pred(T1(i1,j)).
have P := H to i; case P.
(* *)
assert C := (i=i1 || i<>i1).
case C.
(* case i=i1 *)
right.
by exists j.
(* case i<>i1 *)
left.
split.
case (if i = i1 then
       <h3(<<fst(kT(i1)@pred(T1(i1,j))),pin(i1)>,snd(input@T(i1,j))>,key3),
        snd(input@T(i1,j))>
       else kT(i)@pred(T1(i1,j))).
by apply H0 to j'.
(* *)
assert C := (i=i1 || i<>i1).
case C.
(* case i=i1 *)
right.
by exists j.
(* case i<>i1 *)
right.
exists j1.
split.
by case (if i = i1 then
       <h3(<<fst(kT(i1)@pred(T1(i1,j))),pin(i1)>,snd(input@T(i1,j))>,key3),
        snd(input@T(i1,j))>
       else kT(i)@pred(T1(i1,j))).
assert C := (j=j1 || j<>j1).
case C.
apply H1 to j'.
by case H0.
by have Hyp := H1 to j'; case Hyp.

substitute t,T2(i1,j).
have IHA := IH0 to pred(T2(i1,j)).
have P := IHA to i; case P. 
by left; apply H to j'.
right; exists j1; have P := H0 to j'.
by case P.

substitute t,T3(i1,j).
apply IH0 to pred(T3(i1,j)).
apply H0 to i.
case H1.
left. apply H1 to j'.
right. exists j1. apply H1 to j'.
case H2.

substitute t,A(kk).
apply IH0 to pred(A(kk)).
apply H0 to i.
case H1.
left. apply H1 to j'.
right. exists j. apply H1 to j'.
case H2.

substitute t,A1(kk).
apply IH0 to pred(A1(kk)).
apply H0 to i.
case H1.
left. apply H1 to j'.
right. exists j. apply H1 to j'.
case H2.

substitute t,A2(kk).
apply IH0 to pred(A2(kk)).
apply H0 to i.
case H1.
left. apply H1 to j'.
right. exists j. apply H1 to j'.
case H2.
Qed.

goal lastUpdateT :
forall (i,j:index),
  kT(i)@T(i,j) = kT(i)@init
  || (exists (j':index), kT(i)@T(i,j) =
       < h3(<<fst(kT(i)@pred(T1(i,j'))),pin(i)>,snd(input@T(i,j'))>,key3),
         snd(input@T(i,j')) >).
Proof.
intros.
apply lastUpdateTag_ to T(i,j).
apply H0 to i.
case H1.
left.
right.
exists j1.
Qed.

goal lastUpdatePredT1 :
forall (i,j:index),
  kT(i)@pred(T1(i,j)) = kT(i)@init
  || (exists (j':index), kT(i)@pred(T1(i,j)) =
       < h3(<<fst(kT(i)@pred(T1(i,j'))),pin(i)>,snd(input@T(i,j'))>,key3),
         snd(input@T(i,j')) >).
Proof.
intros.
apply lastUpdateTag_ to pred(T1(i,j)).
apply H0 to i.
case H1.
left.
right.
exists j1.
Qed.

goal lastUpdatePredR1 :
forall (jj,ii:index),
  kR(ii)@pred(R1(jj,ii)) = kR(ii)@init
  || (exists (jj':index),
       kR(ii)@pred(R1(jj,ii)) =
         h3(<<kR(ii)@pred(R1(jj',ii)),pin(ii)>,TS@pred(R1(jj',ii))>,key3)).
Proof.
admit. (* TODO probably very similar to lastUpdateT *)
Qed.

goal lastUpdateR :
forall (jj,ii:index),
  kR(ii)@R(jj) = kR(ii)@init
  || (exists (jj':index),
       kR(ii)@R(jj) =
         h3(<<kR(ii)@pred(R1(jj',ii)),pin(ii)>,TS@pred(R1(jj',ii))>,key3)).
Proof.
admit. (* TODO probably very similar to lastUpdatePredT1 *)
Qed.

goal secretStateReader :
forall (t:timestamp), forall (jj,ii:index),
  t < R1(jj,ii) => input@t <> kR(ii)@pred(R1(jj,ii)).
Proof.
induction.
apply lastUpdatePredR1 to jj,ii.
case H0.
(* init case *)
apply stateReaderInit to ii.
fresh M2.
(* general case *)
assert input@t = h3(<<kR(ii)@pred(R1(jj',ii)),pin(ii)>,TS@pred(R1(jj',ii))>,key3).
euf M2.
(* case euf 1/3 - R1(jj1,ii) *)
assert R1(jj',ii) < R1(jj,ii). admit. (* ok *)
case H0.
admit. (* ok *)
admit. (* ok *)
(* case euf 2/3 - T1(i,j) *)
admit. (* TODO *)
(* case euf 3/3 - A2(kk) *)
admit. (* TODO *)
Qed.

goal secretStateTag :
forall (t:timestamp), forall (i,j:index),
  t < T1(i,j) =>
    ( input@t <> <fst(kT(i)@pred(T1(i,j))),pin(i)>
      && input@t <> <<fst(kT(i)@pred(T1(i,j))),pin(i)>,snd(input@T(i,j))> ).
Proof.
induction.
split.

(* case split 1/2 *)
apply lastUpdatePredT1 to i,j.
case H0.
(* init case *)
apply stateTagInit to i.
assert idinit(i) = fst(kT(i)@init).
fresh M3.
(* general case *)
assert fst(input@t) = h3(<<fst(kT(i)@pred(T1(i,j'))),pin(i)>,snd(input@T(i,j'))>,key3).
euf M2.
(* case euf 1/3 - R1(jj,i)  *)
admit.
(* case euf 2/3 - T1(i,j1) *)
assert T1(i,j') < T1(i,j). admit. (* ok *)
case H0.
admit. (* ok *)
admit. (* ok *)
admit. (* ok *)
(* case euf 3/3 - A2(kk) *)
apply IH0 to A2(kk).
apply H1 to i,j'.
admit. (* TODO *)
admit. (* TODO *)
admit. (* TODO *)

(* case split 2/2 *)
apply lastUpdatePredT1 to i,j.
case H0.
(* init case *)
apply stateTagInit to i.
assert idinit(i) = fst(kT(i)@init).
fresh M3.
(* general case *)
assert fst(fst(input@t)) = h3(<<fst(kT(i)@pred(T1(i,j'))),pin(i)>,snd(input@T(i,j'))>,key3).
euf M2.
admit. (* TODO *)
admit. (* TODO *)

apply IH0 to A2(kk).
apply H1 to i,j'.
admit. (* TODO *)
admit. (* TODO *)
admit. (* TODO *)
Qed.



goal auth_R1 :
forall (jj,ii:index),
  cond@R1(jj,ii)
  =>
  (exists (j:index), T(ii,j) < R1(jj,ii) && output@T(ii,j) = input@R1(jj,ii)).
Proof.
intros.
expand cond@R1(jj,ii).

euf M0.

(* case euf 1/2 - T(i,j) *)
assert (i=ii || i<>ii).
case H0.
(* case i=ii - honest case *)
exists j.
(* case i<>ii - absurd, we derive a contradiction *)
apply lastUpdateT to i,j.
apply lastUpdatePredR1 to jj,ii.
case H0.
(* init case *)
apply stateTagInit to i.
apply stateReaderInit to ii.
case H0.
assert h3(<<kR(ii)@pred(R1(jj',ii)),pin(ii)>,TS@pred(R1(jj',ii))>,key3) = idinit(i).
fresh M6.
(* general case *)
case H0.
apply stateReaderInit to ii.
assert idinit(ii) = h3(<<fst(kT(i)@pred(T1(i,j'))),pin(i)>,snd(input@T(i,j'))>,key3).
fresh M5.
assert
  h3(<<fst(kT(i)@pred(T1(i,j'))),pin(i)>,snd(input@T(i,j'))>,key3) =
  h3(<<kR(ii)@pred(R1(jj',ii)),pin(ii)>,TS@pred(R1(jj',ii))>,key3).
collision.

(* case euf 2/2 - A(kk) *)
apply secretStateReader to A(kk).
apply H0 to jj,ii.
Qed.

goal auth_T1 :
forall (i,j:index),
  cond@T1(i,j)
  =>
  (exists (jj:index), R1(jj,i) < T1(i,j) && output@R1(jj,i) = input@T1(i,j)).
Proof.
intros.
expand cond@T1(i,j).
euf M0.
(* case euf 1/2 - honest case R1(jj,i) *)
exists jj.
(* case euf 2/2 - A1(kk) coming from the process oracle *)
apply secretStateTag to A1(kk).
apply H0 to i,j.
Qed.
