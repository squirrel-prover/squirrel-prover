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
    happens(R(j)) =>
    (cond@R(j) <=>
      (exists (i,k:index), T(i,k) < R(j) &&
       fst(output@T(i,k)) = fst(input@R(j)) &&
       snd(output@T(i,k)) = snd(input@R(j)))).
Proof.
  intro *.
  expand cond.
  split.
  project.
  (* LEFT *) by euf Meq; exists i, k0.
  (* RIGHT *) by euf Meq; exists i,k.
  by exists i,k.
Qed.

(* Authentication goal for the action R1 (else branch of the reader) *)

goal wa_R1 :
  forall (j:index),
    happens(R1(j)) =>
    cond@R1(j) <=>
    (not(exists (i,k:index), T(i,k) < R1(j) &&
      fst(output@T(i,k)) = fst(input@R1(j)) &&
      snd(output@T(i,k)) = snd(input@R1(j)))).
Proof.
  intro *.
  expand cond.
  split.
  use H. exists i,k.
  use H.
  project.
  (* LEFT *) by euf Meq; exists i, k0.
  (* RIGHT *) by euf Meq; exists i,k. 
Qed.

(* Equivalence goal expressing unlinkability *)

equiv unlinkability.
Proof.
  induction t.

  (* Case R *)
  expand frame. fa 0. fa 1.
  expand exec, output.
  equivalent
    (cond@R(j)),
    (exists (i,k:index), T(i,k) < R(j) &&
       fst(output@T(i,k))=fst(input@R(j)) &&
       snd(output@T(i,k))=snd(input@R(j))).
  by use wa_R with j.
  by fadup 1. 

  (* Case R1 *)
  expand frame. fa 0. fa 1.
  expand exec, output.
  equivalent
    (cond@R1(j)),
    (not(exists (i,k:index), T(i,k) < R1(j) &&
       fst(output@T(i,k))=fst(input@R1(j)) &&
       snd(output@T(i,k))=snd(input@R1(j)))).
  by use wa_R1 with j.
  by fadup 1.

  (* Case T *)
  expand frame, exec, cond, output.
  fa 0; fa 1; fa 1; fa 1.
  prf 2.
  yesif 2. 
  project.
  split; by fresh Meq.
  split; by fresh Meq.
  fresh 2.
  by fresh 1; yesif 1.
Qed.
