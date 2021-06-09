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

set autoIntro = false.

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

mutable kT(i:index) : message = <idinit(i),TSinit>
mutable kR(ii:index) : message = idinit(ii)
mutable TS : message = TSinit

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

goal lastUpdateTag_ :
forall (t:timestamp), forall (i:index), happens(t) =>
  ((kT(i)@t = kT(i)@init && forall (j':index), happens(T1(i,j')) => t < T1(i,j')) ||
   (exists j:index,
    kT(i)@t = kT(i)@T1(i,j) &&
    T1(i,j) <= t &&
    (forall (j':index), happens(T1(i,j')) => T1(i,j')<=T1(i,j) || t<T1(i,j')))).
Proof.
induction.
intro t IH0 i Hap.
case t.

(* t = init *)
intro _; subst t,init.
left. 
split; 1,2: by auto.

(* t = R(jj) *)
intro _; simpl_left; subst t,R(jj).
use IH0 with pred(R(jj)),i as [[M1 H1] | H2].
left. split.
by expand kT(i)@R(jj); assumption.
intro j' Hap'.
use H1 with j'; 1,2: by constraints.
simpl_left.
right; exists j; split.
expand kT(i)@R(jj).
split; 1,2: by auto.
intro j' Hap'.
use H0 with j' as H1.
case H1.
by left. by right; constraints.
by assumption.
by constraints.
by constraints.

(* t = R1(jj,ii) *)
intro _; simpl_left; subst t,R1(jj,ii).
use IH0 with pred(R1(jj,ii)),i as [[M1 H1] | H2].
left. split.
by expand kT(i)@R1(jj,ii); assumption.
intro j' Hap'.
use H1 with j'; 1,2: by constraints.
simpl_left.
right; exists j; split.
expand kT(i)@R1(jj,ii).
split; 1,2: by auto.
intro j' Hap'.
use H0 with j' as H1.
case H1.
by left. by right; constraints.
by assumption.
by constraints.
by constraints.

(* t = R2(jj) *)
intro _; simpl_left; subst t,R2(jj).
use IH0 with pred(R2(jj)),i as [[M1 H1] | H2].
left. split.
by expand kT(i)@R2(jj); assumption.
intro j' Hap'.
use H1 with j'; 1,2: by constraints.
simpl_left.
right; exists j; split.
expand kT(i)@R2(jj).
split; 1,2: by auto.
intro j' Hap'.
use H0 with j' as H1.
case H1.
by left. by right; constraints.
by assumption.
by constraints.
by constraints.

(* t = T(i0,j) *)
intro _; simpl_left; subst t,T(i0,j).
use IH0 with pred(T(i0,j)),i as [[M1 H1] | H2].
left. split.
by expand kT(i)@T(i0,j); assumption.
intro j' Hap'.
use H1 with j'; 1,2: by constraints.
simpl_left.
right; exists j0; split.
expand kT(i)@T(i0,j).
split; 1,2: by auto.
intro j' Hap'.
use H0 with j' as H1.
case H1.
by left. by right; constraints.
by assumption.
by constraints.
by constraints.

(* t = T1(i0,j) - interesting case *)
intro _; simpl_left; subst t,T1(i0,j).
use IH0 with pred(T1(i0,j)),i as H.
case H. 

(* case H 1/2 *)
destruct H as [H1 H2].
assert (i=i0 || i<>i0) as C.
by constraints.
case C.
(* case i=i0 *)
right.
exists j.
split. split.
by congruence. by constraints.
intro j' Hap'.
use H2 with j' as Ht; 2: by assumption.
assert (j=j' || j<>j') as C'.
by constraints.
case C'.
by left.
by right; constraints.
(* case i<>i0 *)
left.
split.
expand kT(i)@T1(i0,j).
case (if i = i0 then
       <h3(<<fst(kT(i0)@pred(T1(i0,j))),pin(i0)>,snd(input@T(i0,j))>,key3),
        snd(input@T(i0,j))>
       else kT(i)@pred(T1(i0,j))).
intro H3.
destruct H3 as [H4 H5].
by constraints.
intro H3.
destruct H3 as [H4 H5].
by assumption.
intro j' Hap'.
use H2 with j' as Ht; 2: by assumption.
assert (j=j' || j<>j') as C'.
by constraints.
case C'.
by constraints.
by constraints.

(* case H 2/2 *)
simpl_left.
assert (i=i0 || i<>i0) as C.
by constraints.
case C.
assert (j=j0 || j<>j0) as C'.
by constraints.
case C'.

(* case i=i0 && j=j0 *)
by constraints.

(* case i=i0 && j<>j0 *)
right.
exists j.
split. split.
by congruence.
by constraints.
intro j' Hap'.
use H0 with j' as Ht; 2: by assumption.
case Ht.
by left; constraints.
assert (j=j' || j<>j') as C.
by constraints.
case C.
by left; constraints.
by right; constraints.

(* case i<>i0 *)
right.
exists j0.
split. split.
expand kT(i)@T1(i0,j).
case (if i = i0 then
   <h3(<<fst(kT(i0)@pred(T1(i0,j))),pin(i0)>,snd(input@T(i0,j))>,key3),
    snd(input@T(i0,j))>
   else kT(i)@pred(T1(i0,j))).
intro H2.
destruct H2 as [H3 H4].
by constraints.
intro H2.
destruct H2 as [H3 H4].
by assumption.

by constraints.
intro j' Hap'.
use H0 with j' as Ht; 2: by assumption.
case Ht.
by left; constraints.
assert (j=j' || j<>j') as C'.
by constraints.
case C'.
by right; constraints.
by right; constraints.
by constraints.
by constraints.

(* t = T2(i0,j) *)
intro _; simpl_left; subst t,T2(i0,j).
use IH0 with pred(T2(i0,j)),i as [[M1 H1] | H2].
left. split.
by expand kT(i)@T2(i0,j); assumption.
intro j' Hap'.
use H1 with j'; 1,2: by constraints.
simpl_left.
right; exists j0; split.
expand kT(i)@T2(i0,j).
split; 1,2: by auto.
intro j' Hap'.
use H0 with j' as H1.
case H1.
by left. by right; constraints.
by assumption.
by constraints.
by constraints.

(* t = T3(i0,j) *)
intro _; simpl_left; subst t,T3(i0,j).
use IH0 with pred(T3(i0,j)),i as [[M1 H1] | H2].
left. split.
by expand kT(i)@T3(i0,j); assumption.
intro j' Hap'.
use H1 with j'; 1,2: by constraints.
simpl_left.
right; exists j0; split.
expand kT(i)@T3(i0,j).
split; 1,2: by auto.
intro j' Hap'.
use H0 with j' as H1.
case H1.
by left. by right; constraints.
by assumption.
by constraints.
by constraints.

(* t = A(kk) *)
intro _; simpl_left; subst t,A(kk).
use IH0 with pred(A(kk)),i as [[M1 H1] | H2].
left. split.
by expand kT(i)@A(kk); assumption.
intro j' Hap'.
use H1 with j'; 1,2: by constraints.
simpl_left.
right; exists j; split.
expand kT(i)@A(kk).
split; 1,2: by auto.
intro j' Hap'.
use H0 with j' as H1.
case H1.
by left. by right; constraints.
by assumption.
by constraints.
by constraints.

(* t = A1(kk) *)
intro _; simpl_left; subst t,A1(kk).
use IH0 with pred(A1(kk)),i as [[M1 H1] | H2].
left. split.
by expand kT(i)@A1(kk); assumption.
intro j' Hap'.
use H1 with j'; 1,2: by constraints.
simpl_left.
right; exists j; split.
expand kT(i)@A1(kk).
split; 1,2: by auto.
intro j' Hap'.
use H0 with j' as H1.
case H1.
by left. by right; constraints.
by assumption.
by constraints.
by constraints.

(* t = A2(kk) *)
intro _; simpl_left; subst t,A2(kk).
use IH0 with pred(A2(kk)),i as [[M1 H1] | H2].
left. split.
by expand kT(i)@A2(kk); assumption.
intro j' Hap'.
use H1 with j'; 1,2: by constraints.
simpl_left.
right; exists j; split.
expand kT(i)@A2(kk).
split; 1,2: by auto.
intro j' Hap'.
use H0 with j' as H1.
case H1.
by left. by right; constraints.
by assumption.
by constraints.
by constraints.
Qed.

goal lastUpdateT :
forall (i,j:index), happens(T(i,j)) =>
  (kT(i)@T(i,j) = kT(i)@init
   || (exists (j':index), kT(i)@T(i,j) =
       < h3(<<fst(kT(i)@pred(T1(i,j'))),pin(i)>,snd(input@T(i,j'))>,key3),
         snd(input@T(i,j')) >)).
Proof.
intro i j Hap.
use lastUpdateTag_ with T(i,j),i as H1; 2: by assumption.
case H1.
by left.
right; simpl_left.
exists j0.
by expand kT(i)@T1(i,j0); assumption.
Qed.

goal lastUpdatePredT1 :
forall (i,j:index), happens(T1(i,j)) =>
  (kT(i)@pred(T1(i,j)) = kT(i)@init
   || (exists (j':index), kT(i)@pred(T1(i,j)) =
       < h3(<<fst(kT(i)@pred(T1(i,j'))),pin(i)>,snd(input@T(i,j'))>,key3),
         snd(input@T(i,j')) >)).
Proof.
intro i j Hap.
use lastUpdateTag_ with pred(T1(i,j)),i as H1; 2: by constraints.
case H1.
by left.
simpl_left. right. exists j0.
expand kT(i)@T1(i,j0).
by congruence.
Qed.

goal lastUpdatePredR1 :
forall (jj,ii:index), happens(pred(R1(jj,ii))) =>
  (kR(ii)@pred(R1(jj,ii)) = kR(ii)@init
   || (exists (jj':index), R1(jj',ii) <= pred(R1(jj,ii)) &&
       kR(ii)@pred(R1(jj,ii)) =
         h3(<<kR(ii)@pred(R1(jj',ii)),pin(ii)>,TS@pred(R1(jj',ii))>,key3))).
Proof.
admit. (* TODO probably very similar to lastUpdateT *)
Qed.

goal lastUpdateR :
forall (jj,ii:index), happens(R(jj)) =>
  (kR(ii)@R(jj) = kR(ii)@init
   || (exists (jj':index),
       kR(ii)@R(jj) =
         h3(<<kR(ii)@pred(R1(jj',ii)),pin(ii)>,TS@pred(R1(jj',ii))>,key3))).
Proof.
admit. (* TODO probably very similar to lastUpdatePredT1 *)
Qed.

goal secretStateReader :
forall (t:timestamp), forall (jj,ii:index), happens(R1(jj,ii)) =>
  (t < R1(jj,ii) => input@t <> kR(ii)@pred(R1(jj,ii))).
Proof.
admit.
(*
induction.
intro t H jj ii Hap Ht.
use lastUpdatePredR1 with jj,ii as H0.
case H0.
(* init case *)
expand kR(ii)@init.
admit. (* FRESH *)
(* general case *)
assert
  input@t = h3(<<kR(ii)@pred(R1(jj',ii)),pin(ii)>,TS@pred(R1(jj',ii))>,key3) as M2.
euf M2.
(* case euf 1/3 - R1(jj1,ii) *)
assert R1(jj',ii) < R1(jj,ii) as H1. admit. (* ok *)
case H0.
admit. (* ok *)
admit. (* ok *)
(* case euf 2/3 - T1(i,j) *)
admit. (* TODO *)
(* case euf 3/3 - A2(kk) *)
admit. (* TODO *)
*)
Qed.

goal secretStateTag :
forall (t:timestamp), forall (i,j:index), happens(T1(i,j)) =>
  (t < T1(i,j) =>
    ( input@t <> <fst(kT(i)@pred(T1(i,j))),pin(i)>
      && input@t <> <<fst(kT(i)@pred(T1(i,j))),pin(i)>,snd(input@T(i,j))> )).
Proof.
admit.
(*
nosimpl(induction; intro IH i j).
intro *.
split.

(* case split 1/2 *)
use lastUpdatePredT1 with i,j as H0.
case H0.
(* init case *)
assert idinit(i) = fst(kT(i)@init) as M3.
admit. (* FRESH *)
(* general case *)
assert
  fst(input@t) = h3(<<fst(kT(i)@pred(T1(i,j'))),pin(i)>,snd(input@T(i,j'))>,key3)
  as M2.
euf M2.
(* case euf 1/3 - R1(jj,i)  *)
admit.
(* case euf 2/3 - T1(i,j1) *)
assert T1(i,j') < T1(i,j) as H1. admit. (* ok *)
case H.
admit. (* ok *)
admit. (* ok *)
admit. (* ok *)
(* case euf 3/3 - A2(kk) *)
use IH with A2(kk),i,j' as H1.
admit. (* TODO *)
admit. (* TODO *)
admit. (* TODO *)

(* case split 2/2 *)
use lastUpdatePredT1 with i,j as H0.
case H0.
(* init case *)
assert idinit(i) = fst(kT(i)@init) as M3.
admit. (* FRESH *)
(* general case *)
assert
  fst(fst(input@t)) =
  h3(<<fst(kT(i)@pred(T1(i,j'))),pin(i)>,snd(input@T(i,j'))>,key3)
  as M2.
euf M2.
admit. (* TODO *)
admit. (* TODO *)

use IH with A2(kk),i,j' as H2.
admit. (* TODO *)
admit. (* TODO *)
admit. (* TODO *)
*)
Qed.

goal stateIdReader :
forall (t:timestamp), forall (i,ii:index), happens(t) =>
  (i <> ii => kR(ii)@t <> idinit(i)).
Proof.
induction.
intro t IH0 i ii Hap Hi.
case t.
intro _; subst t,init.
expand kR(ii)@init.
by eqnames.

intro _; simpl_left; subst t,R(jj).
expand kR(ii)@R(jj).
use IH0 with pred(R(jj)),i,ii as H; 2,3,4: by constraints.
by assumption.

intro _; simpl_left; subst t,R1(jj,ii0).
(*expand kR(ii)@R1(jj,ii0).*)
case (if ii = ii0 then
   h3(<<kR(ii0)@pred(R1(jj,ii0)),pin(ii0)>,TS@pred(R1(jj,ii0))>,key3) else
   kR(ii)@pred(R1(jj,ii0))).
assert (ii=ii0 || ii<>ii0) as H.
by constraints.
case H.
intro H1.
destruct H1 as [H2 H3].
expand kR(ii)@R1(jj,ii).
intro M.
use IH0 with pred(R1(jj,ii)),i,ii as H4; 2,3,4: by constraints.
fresh M.
admit. (* TODO - fresh tactic not precise enough *)
intro _.
by constraints.
assert (ii=ii0 || ii<>ii0) as H.
by constraints.
case H.
intro _.
by constraints.
intro H1.
destruct H1 as [H2 H3].
use IH0 with pred(R1(jj,ii0)),i,ii as H4; 2,3,4: by constraints.
expand kR(ii)@R1(jj,ii0).
intro _.
assert kR(ii)@pred(R1(jj,ii0)) = idinit(i). admit.
by congruence.

intro _; simpl_left; subst t,R2(jj).
expand kR(ii)@R2(jj).
use IH0 with pred(R2(jj)),i,ii as H; 2,3,4: by constraints.
by assumption.

intro _; simpl_left; subst t,T(i0,j).
expand kR(ii)@T(i0,j).
use IH0 with pred(T(i0,j)),i,ii as H; 2,3,4: by constraints.
by assumption.

intro _; simpl_left; subst t,T1(i0,j).
expand kR(ii)@T1(i0,j).
use IH0 with pred(T1(i0,j)),i,ii as H; 2,3,4: by constraints.
by assumption.

intro _; simpl_left; subst t,T2(i0,j).
expand kR(ii)@T2(i0,j).
use IH0 with pred(T2(i0,j)),i,ii as H; 2,3,4: by constraints.
by assumption.

intro _; simpl_left; subst t,T3(i0,j).
expand kR(ii)@T3(i0,j).
use IH0 with pred(T3(i0,j)),i,ii as H; 2,3,4: by constraints.
by assumption.

intro _; simpl_left; subst t,A(kk).
expand kR(ii)@A(kk).
use IH0 with pred(A(kk)),i,ii as H; 2,3,4: by constraints.
by assumption.

intro _; simpl_left; subst t,A1(kk).
expand kR(ii)@A1(kk).
use IH0 with pred(A1(kk)),i,ii as H; 2,3,4: by constraints.
by assumption.

intro _; simpl_left; subst t,A2(kk).
expand kR(ii)@A2(kk).
use IH0 with pred(A2(kk)),i,ii as H; 2,3,4: by constraints.
by assumption.
Qed.

goal stateIdTag :
forall (t:timestamp), forall (i,ii:index), happens(t) =>
  (i <> ii => fst(kT(i)@t) <> idinit(ii)).
Proof.
admit.
Qed.


goal auth_R1 :
forall (jj,ii:index), happens(R1(jj,ii)) =>
  (cond@R1(jj,ii)
  =>
  (exists (j:index), T(ii,j) < R1(jj,ii) && output@T(ii,j) = input@R1(jj,ii))).
Proof.
intro jj ii Hap Hcond.
expand cond@R1(jj,ii).
euf Hcond.

(* case euf 1/2 - T(i,j) *)
assert (i=ii || i<>ii) as H0.
by constraints.
case H0.
(* case i=ii - honest case *)
intro Ht M.
exists j.
expand output@T(i,j).
split; 1,2: by auto.
(* case i<>ii - absurd, we derive a contradiction *)
intro Ht M.
use lastUpdateT with i,j as H1; 2: by constraints.
use lastUpdatePredR1 with jj,ii as H2; 2: by constraints.
case H1. case H2.
(* kT(i)@T(i,j) = kT(i)@init && kR(ii)@pred(R1(jj,ii)) = kR(ii)@init  *)
expand kT(i)@init.
expand kR(ii)@init.
assert idinit(i) = idinit(ii). by congruence.
by eqnames.
(* kT(i)@T(i,j) = kT(i)@init && kR(ii)@pred(R1(jj,ii)) = h3(...) *)
simpl_left.
expand kT(i)@init.
use stateIdReader with pred(R1(jj,ii)),i,ii as H2; 2,3: by auto.
by congruence.

case H2.
(* kT(i)@T(i,j) = <h3(...),...> && kR(ii)@pred(R1(jj,ii)) = kR(ii)@init *)
simpl_left.
expand kR(ii)@init.
use stateIdTag with T(i,j),i,ii as H3; 2,3: by auto.
by congruence.
(* kT(i)@T(i,j) = <h3(...),...> && kR(ii)@pred(R1(jj,ii)) = h3(...) *)
simpl_left.
assert
  h3(<<fst(kT(i)@pred(T1(i,j'))),pin(i)>,snd(input@T(i,j'))>,key3) =
  h3(<<kR(ii)@pred(R1(jj',ii)),pin(ii)>,TS@pred(R1(jj',ii))>,key3)
  as _.
by congruence.
collision.
intro _.
assert pin(i) = pin(ii).
by congruence.
by eqnames.

(* case euf 2/2 - A(kk) *)
intro Ht M.
use secretStateReader with A(kk),jj,ii.
by congruence.
by constraints.
by assumption.
Qed.

goal auth_T1 :
forall (i,j:index), happens(T1(i,j)) =>
  (cond@T1(i,j)
  =>
  (exists (jj:index), R1(jj,i) < T1(i,j) && output@R1(jj,i) = input@T1(i,j))).
Proof.
intro i j Hap Hcond.
expand cond@T1(i,j).
euf Hcond.
(* case euf 1/2 - honest case R1(jj,ii) *)
intro Ht M.
assert pin(i) = pin(ii). by congruence.
eqnames.
exists jj.
expand output@R1(jj,ii). expand m(jj,ii)@R1(jj,ii).
split; 1,2: by auto.
(* case euf 2/2 - A1(kk) coming from the process oracle *)
intro Ht M.
use secretStateTag with A1(kk),i,j.
by congruence.
by assumption.
by assumption.
Qed.
