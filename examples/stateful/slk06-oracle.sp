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
         
COMMENTS
- In this model, we add parallel processes to the global system to model the 
fact that the attacker can hash messages.
In order to prove the authentication goals, we have to prove that an input
cannot be equal to some values, ie that values stored in states are not
deducible.
The corresponding goals secretStateTag and secretStateReader are not yet proven.
- TODO refine fresh and congruence to remove admit in stateInitX goals.

PROOFS
- lastUpdateTag / lastUpdateReader
- stateInitTag / stateInitReader
- authentication (reader and tag)
*******************************************************************************)

set autoIntro = false.

abstract ok : message
abstract error : message

abstract TSinit : message
abstract (~<) : message -> message -> boolean
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
  if fst(x1) = h(snd(x1),k) && snd(kT(i)) ~< snd(x1) then
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


(* LIBRARIES *)

include Basic.

(* PROOF *)

goal lastUpdateTag (t:timestamp, i:index) :
  happens(t) =>
  (kT(i)@t = kT(i)@init 
   && forall (j':index), happens(T1(i,j')) => t < T1(i,j')) 
   ||
   exists j:index,
    kT(i)@t = kT(i)@T1(i,j) && T1(i,j) <= t &&
    forall (j':index), 
     happens(T1(i,j')) => T1(i,j')<=T1(i,j) || t<T1(i,j').
Proof.
  generalize i; induction t.
  intro t IH0 i Hap.
  case t;
  try (
  intro Eq; repeat destruct Eq as [_ Eq]; 
  use IH0 with pred(t),i as [[M1 H1] | [mj [_ H2]]] => //;
  [ 1: left; 
       (split; 1:auto); 
       intro j' _;
       by use H1 with j' |
    2: right; exists mj; 
       (split; 1: auto);
       intro j' _;
       by use H2 with j' as H1; 1: case H1]).


  (* t = init *)
  by intro _; left.

  (* t = T1(i0,j) - interesting case *)
  intro [i0 j Eq]; subst t,T1(i0,j).
  use IH0 with pred(T1(i0,j)),i as H => //.
  case H. 

  (* case H - 1/2 *)
  destruct H as [H1 H2].
  case (i=i0) => C.

  (* case i=i0 *)
  right.
  exists j. 
  simpl.
  intro j' Hap'.
  use H2 with j' as Ht; 2: assumption.
  by case (j=j').

  (* case i<>i0 *)
  left.
  split.
  expand kT.
  by case (i = i0).
  intro j' Hap'.
  use H2 with j' as Ht; 2: assumption.
  by case (j=j'). 

  (* case H - 2/2 *)
  destruct H as [j0 [_ H0]].
  case (i=i0) => C. 
  case (j=j0) => C' //. 

  (* case i=i0 && j<>j0 *)
  right.
  exists j. simpl.
  intro j' Hap'.
  by use H0 with j' as Ht.

  (* case i<>i0 *)
  right.
  exists j0.
  simpl.
  split. 
  expand kT. 
  by case (i = i0).

  intro j' Hap'.
  by use H0 with j' as Ht; 1: case Ht.
Qed.


goal lastUpdateT :
forall (i,j:index), happens(T(i,j)) =>
  (kT(i)@T(i,j) = kT(i)@init
   || (exists (j':index), kT(i)@T(i,j) =
       < h3(<<fst(kT(i)@pred(T1(i,j'))),pin(i)>,snd(input@T(i,j'))>,key3),
         snd(input@T(i,j')) >)).
Proof.
  intro i j Hap.
  use lastUpdateTag with T(i,j),i as H1; 2: assumption.
  case H1.
  by left.
  right.
  destruct H1 as [j0 _].
  by exists j0.
Qed.


goal lastUpdateReader_ :
  forall (t:timestamp), forall (ii:index), happens(t) =>
    ( (kR(ii)@t = kR(ii)@init 
        && forall (jj':index), happens(R1(jj',ii)) => t < R1(jj',ii)) 
      ||
      (exists jj:index,
        kR(ii)@t = kR(ii)@R1(jj,ii) && R1(jj,ii) <= t &&
        (forall (jj':index), 
          happens(R1(jj',ii)) => R1(jj',ii)<=R1(jj,ii) || t<R1(jj',ii)))).
Proof.
  induction.
  intro t IH0 ii Hap.
  case t;
  try (
  intro Eq; repeat destruct Eq as [_ Eq];
  use IH0 with pred(t),ii as [[M1 H1] | [mj [_ H2]]] => //;
  [ 1: left; 
       (split; 1:auto); 
       intro j' _;
       by use H1 with j' |
    2: right; exists mj; 
       (split; 1: auto);
       intro j' _;
       by use H2 with j' as H1; 1: case H1]).

  (* t = init *)
  by intro _; left. 

  (* t = R1(jj,ii0) - interesting case *)
  intro [jj ii0 Eq].
  use IH0 with pred(R1(jj,ii0)),ii as H => //.
  case H. 

  (* case H - 1/2 *)
  destruct H as [H1 H2].
  case (ii=ii0) => _.

  (* case ii=ii0 *)
  right.
  exists jj.
  simpl.
  intro jj' _.
  use H2 with jj' as Ht; 2: assumption.
  case (jj=jj') => _.
  by left.
  by right.

  (* case i<>i0 *)
  left. 
  split.
  expand kR.
  by case (ii = ii0). 
  intro jj' Hap'.
  use H2 with jj' as Ht; 2: assumption.
  by case (jj=jj').

  (* case H - 2/2 *)
  destruct H as [jj0 [_ _ H0]].
  case (ii=ii0) => C.
  case (jj=jj0) => C'.

  (* case ii=ii0 && jj=jj0 *)
  constraints.

  (* case ii=ii0 && jj<>jj0 *)
  right.
  exists jj.
  simpl.
  intro jj' Hap'.
  use H0 with jj' as Ht; 2: assumption.
  case Ht.
  by left.
  by case (jj=jj').

  (* case ii<>ii0 *)
  right.
  exists jj0.
  simpl.
  split.
  expand kR.
  by case (ii = ii0). 

  intro jj' Hap'.
  use H0 with jj' as Ht; 2: assumption.
  case Ht.
  by left.
  by case (jj=jj').
Qed.


goal lastUpdatePredR1 (jj,ii:index) :
  happens(pred(R1(jj,ii))) =>
 (kR(ii)@pred(R1(jj,ii)) = kR(ii)@init
   || 
   exists (jj':index), 
     R1(jj',ii) <= pred(R1(jj,ii)) &&
     kR(ii)@pred(R1(jj,ii)) =
         h3(<<kR(ii)@pred(R1(jj',ii)),pin(ii)>,TS@pred(R1(jj',ii))>,key3)).
Proof.
  intro Hap.
  use lastUpdateReader_ with pred(R1(jj,ii)),ii as H1; 2: assumption.
  case H1.
  by left.
  right. 
  destruct H1 as [jj0 _]. 
  by exists jj0.
Qed.

goal secretStateReader (t:timestamp, jj,ii:index):
  happens(R1(jj,ii)) =>
  t < R1(jj,ii) => 
  input@t = kR(ii)@pred(R1(jj,ii)) =>
  False.
Proof.
  admit.
Qed.

goal secretStateTag (t:timestamp, i,j:index):
  happens(T1(i,j)) =>
  t < T1(i,j) =>
  ( input@t <> <fst(kT(i)@pred(T1(i,j))),pin(i)> && 
    input@t <> <<fst(kT(i)@pred(T1(i,j))),pin(i)>,snd(input@T(i,j))> ).
Proof.
  admit.
Qed.

goal stateInitReader (t:timestamp, i,ii:index):
  happens(t) => i <> ii => kR(ii)@t <> idinit(i).
Proof.
  generalize i ii.
  induction t.
  intro t IH0 i ii Hap Hi.
  case t;
  intro A;
  repeat destruct A as [_ A];
  try (by expand kR; apply IH0).

  (* init *)
  auto.

  (* case t = R1(jj,ii0) - interesting case *)
  case (ii = ii0) => _. 
  expand kR.
  intro M.
  use IH0 with pred(R1(jj,ii)),i,ii as H4 => //.
  by fresh M.

  case (ii=ii0) => _ //. 
  expand kR. 
  rewrite if_false //. 
  by apply IH0.
Qed.


goal stateInitTag (t:timestamp, i,ii:index):
  happens(t) =>
  (i <> ii => fst(kT(i)@t) <> idinit(ii)).
Proof.
  generalize i ii.
  induction t.
  intro t IH0 i ii Hap Hi.
  case t;
  intro A;
  repeat destruct A as [_ A];
  try (by expand kT; apply IH0).

  auto.

  (* case t = T1(i0,j) - interesting case *)
  case (i = i0) => _.
  intro M.
  use IH0 with pred(T1(i,j)),i,ii as _ => //. 
  fresh M.
  admit. 
   (* TODO - fresh tactic not precise enough *)
   (* Adrien: I believe this is not true: kT depends on `input`, 
              hence even a precise fresh does not allow to conclude here. *)

  case (i=i0) => _ //=. 
  expand kT. 
  rewrite if_false //. 
  by apply IH0.
Qed.


goal auth_R1 (jj,ii:index):
  happens(R1(jj,ii)) =>
  cond@R1(jj,ii) =>
  exists (j:index), 
   T(ii,j) < R1(jj,ii) && output@T(ii,j) = input@R1(jj,ii).
Proof.
  intro Hap Hcond.
  expand cond.
  euf Hcond.

  (* case euf 1/2 - T(i,j) *)
  case (i=ii) => _; 1: by intro *; exists j. 

  (* case i<>ii - absurd, we derive a contradiction *)
  intro Ht M.
  use lastUpdateT with i,j as H1; 2: constraints.
  use lastUpdatePredR1 with jj,ii as H2; 2: constraints.
  case H1. case H2.
  (* kT(i)@T(i,j) = kT(i)@init && kR(ii)@pred(R1(jj,ii)) = kR(ii)@init  *)
  auto.
  (* kT(i)@T(i,j) = kT(i)@init && kR(ii)@pred(R1(jj,ii)) = h3(...) *)
  expand kT.
  (* TODO: Adrien: instead of stateInitReader, we can do *)
  (* rewrite H1 /= in M. *)
  (* and use the fact that kR is strongly secret at time 
     kR(ii)@pred(R1(jj,ii)) *)
  by use stateInitReader with pred(R1(jj,ii)),i,ii.

  destruct H1 as [j' H1]. 
  case H2.
  (* kT(i)@T(i,j) = <h3(...),...> && kR(ii)@pred(R1(jj,ii)) = kR(ii)@init *)
  expand kR.
  (* TODO: Adrien: instead of stateInitTag, we can use the fact that kR is
     strongly secret at time kR(ii)@pred(R1(jj,ii)) in hypothesis H2*)
  by use stateInitTag with T(i,j),i,ii.

  (* kT(i)@T(i,j) = <h3(...),...> && kR(ii)@pred(R1(jj,ii)) = h3(...) *)
  destruct H2 as [jj' H2].
  assert
    h3(<<fst(kT(i)@pred(T1(i,j'))),pin(i)>,snd(input@T(i,j'))>,key3) =
    h3(<<kR(ii)@pred(R1(jj',ii)),pin(ii)>,TS@pred(R1(jj',ii))>,key3)
    as _. 
  congruence.  
  clear H1 H2 M Hcond.
  by collision.

  (* case euf 2/2 - A(kk) *)
  by intro *; use secretStateReader with A(kk),jj,ii.
Qed.


goal auth_T1 (i,j:index):
  happens(T1(i,j)) =>
  cond@T1(i,j) =>
  exists (jj:index), 
   R1(jj,i) < T1(i,j) && output@R1(jj,i) = input@T1(i,j).
Proof.
intro Hap Hcond.
expand cond.
euf Hcond.
(* case euf 1/2 - honest case R1(jj,ii) *)
intro Ht [_ M].
by exists jj.

(* case euf 2/2 - A1(kk) coming from the process oracle *)
by intro *; use secretStateTag with A1(kk),i,j.
Qed.
