(*******************************************************************************
BASIC HASH

[A] Mayla Brusò, Kostas Chatzikokolakis, and Jerry den Hartog. Formal
Verification of Privacy for RFID Systems. pages 75–88, July 2010.

T --> R : <nT, h(nT,kT)>
R --> T : ok
*******************************************************************************)

hash h

abstract ok : message
abstract ko : message

name key : index->message
name key' : index->index->message

channel cT
channel cR

process tag(i:index,k:index) =
  new nT;
  out(cT, <nT, h(nT,diff(key(i),key'(i,k)))>)

process reader(j:index) =
  in(cT,x);
  if exists (i,k:index), snd(x) = h(fst(x),diff(key(i),key'(i,k))) then
    out(cR,ok)
  else
    out(cR,ko)

system ((!_j R: reader(j)) | (!_i !_k T: tag(i,k))).

(* Authentication goal for the action R (then branch of the reader) *)

goal wa_R :
  forall (j:index),
    cond@R(j) <=>
    (exists (i,k:index), T(i,k) < R(j) &&
      fst(output@T(i,k)) = fst(input@R(j)) &&
      snd(output@T(i,k)) = snd(input@R(j))).
Proof.
  intros.
  expand cond@R(j).
  split.
  project.
  (* LEFT *) euf M0. exists i, k1.
  (* RIGHT *) euf M0. exists i,k.
  exists i,k.
Qed.

(* Authentication goal for the action R1 (else branch of the reader) *)

goal wa_R1 :
  forall (j:index),
    cond@R1(j) <=>
    (not(exists (i,k:index), T(i,k) < R1(j) &&
      fst(output@T(i,k)) = fst(input@R1(j)) &&
      snd(output@T(i,k)) = snd(input@R1(j)))).
Proof.
  intros.
  expand cond@R1(j).
  split.
  apply H0. exists i,k.
  apply H0.
  project.
  (* LEFT *) euf M0. exists i, k1.
  (* RIGHT *) euf M0. exists i,k.
Qed.

(* Equivalence goal expressing unlinkability *)

equiv unlinkability.
Proof.
  induction t.

  (* Case R *)
  expand frame@R(j). fa 0. fa 1.
  expand exec@R(j). expand output@R(j).
  equivalent
    (cond@R(j)),
    (exists (i,k:index), T(i,k) < R(j) &&
       fst(output@T(i,k))=fst(input@R(j)) &&
       snd(output@T(i,k))=snd(input@R(j))).
  apply wa_R to j.
  fadup 1.

  (* Case R1 *)
  expand frame@R1(j). fa 0. fa 1.
  expand exec@R1(j). expand output@R1(j).
  equivalent
    (cond@R1(j)),
    (not(exists (i,k:index), T(i,k) < R1(j) &&
       fst(output@T(i,k))=fst(input@R1(j)) &&
       snd(output@T(i,k))=snd(input@R1(j)))).
  apply wa_R1 to j.
  fadup 1.

  (* Case T *)
  expand frame@T(i,k); expand exec@T(i,k).
  expand cond@T(i,k); expand output@T(i,k).
  fa 0. fa 1. fa 1. fa 1.
  prf 2.
  yesif 2. project.
  split.
  fresh M0.
  fresh M0.
  split.  
  fresh M0.
  fresh M0.
  fresh 2.
  fresh 1. yesif 1.
Qed.
