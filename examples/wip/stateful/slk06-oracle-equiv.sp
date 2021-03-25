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
Trying to prove the secret of the states with an equivalence.
*******************************************************************************)

set autoIntro=false.

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
name fresh : message

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

equiv strong_sec (t,t':timestamp,ii:index) : [happens(t,t')] -> frame@t, diff(kR(ii)@t',fresh).
Proof.
intro Hap.
induction t.

(* case t = init *)
induction t'.
  (* case t' = init *)
  equivalent kR(ii)@init,idinit(ii); 1: auto.
  expand frame@init.
  fresh 0. 
  yesif 0. auto.
  (* case t' = R1(jj,ii1) *)
  admit. (* lastUpdate pour exprimer kR avec h3 puis PRF *)
  (* case t' = ... *)
  admit. admit. admit. admit. admit. admit. admit. admit. admit.

(* case t = R(jj) *)
admit.

(* case t = R1(jj,ii1) *)
expandall.
fa 0. fa 1. fa 2.
admit 1. (* on a besoin de cond => honest pour faire du FADUP ??? or on a besoin du secret pour prouver cond => honest... *)
prf 1.
yesif 1. 
admit.
fresh 1.
admit.

(* case t = R2(jj) *)
admit. (* similar to R1(jj,ii1) *)

(* case t = T(i,j) *)
admit.

(* case t = T1(i,j) *)
admit.

(* case t = T2(i,j) *)
admit.

(* case t = T3(i,j) *)
admit.

(* case t = A(kk) *)
admit.

(* case t = A1(kk) *)
admit.

(* case t = A2(kk) *)
admit.
Qed.
