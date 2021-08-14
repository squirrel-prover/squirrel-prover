(*******************************************************************************

Internet Key Exchange (IKE) Version 2, with Signatures

Defined in RFC7296 -> https://datatracker.ietf.org/doc/html/rfc7296

Extended with an additional pre-shared key for PQ soundness as described in https://datatracker.ietf.org/doc/html/rfc8784


# Protocol Description

We consider the phase 1 with digital signatures.

1. I → R : HDR 1, SAi1, g xA , N A
2. R → I : HDR 2, SAr1, g xB , N B
3. I → R : HDR 3, {IDA, IDB, AUTHi, SAi2, T Si, T Sr }SK
4. R → O : HDR 4, {IDB, AUTHr, SAr2, T Si, T Sr }SK

            Initiator                        Responder
           -----------                      -----------
            HDR, SA, g^a, Ni, IDii -->
                                  <--    HDR, SA, g^b, Nr, IDir, HASH_R
            HDR, HASH_I           -->


where
    HASH_I = prf(SKEYID, g^xi | g^xr | CKY-I | CKY-R | SAi_b | IDii_b )
    HASH_R = prf(SKEYID, g^xr | g^xi | CKY-R | CKY-I | SAi_b | IDir_b )
The final pre-key is SKEYID := prf(psk, Ni_b | Nr_b),
 a final key is       SKEYID_d = prf(SKEYID, g^xy | CKY-I | CKY-R | 0)


 We abstract away from implementation details, and model the key exchange as:


            Initiator                        Responder
           -----------                      -----------
            g^a, Ni, IDii -->
                                  <--    g^b, Nr, IDir, HASH_R
            HASH_I           -->


*******************************************************************************)

set postQuantumSound = true.

hash h

(* pre-shared keys *)
name psk : index -> index -> message

(* DDH randomnesses *)
name a : index -> message
name b : index -> message

abstract g : message
abstract exp : message -> message -> message

(* fresh randomness *)
name Ni : index -> message
name Nr : index -> message

(* identities *)
name IdI : index -> message
name IdR : index -> message

abstract ok:message
abstract ko:message

channel cI
channel cR.

process Initiator(i:index) =
  out(cI, <exp(g,a(i)), < Ni(i), IdI(i) >>);
  in(cI, m);
  let gB = fst(m) in
  let RNr = fst(snd(m)) in
  let RIdR = fst(snd(snd(m))) in
  let HashR = snd(snd(snd(m))) in
  (* find the preshared key in the database corresponding to the identity *)
  try find j such that RIdR = IdR(j) in
    let skeyid = h(<Ni(i),RNr > ,psk(i,j)) in
    if HashR =  h(<gB, < exp(g,a(i))  , IdI(i)> > ,skeyid) then
       out(cI, ok)
       (* Missing last part... *)
process Responder(j:index) =
  in(cI, m);
  let gA  = fst(m) in
  let RNi = fst(snd(m)) in
  let RIdI = snd(snd(m)) in
  (* find the preshared key in the database corresponding to the identity *)
  try find i such that RIdI = IdI(i) in
    let skeyid = h(<RNi,Nr(j) > ,psk(i,j)) in
    out(cR, <exp(g,b(j)), <Nr(j), < IdR(j)  ,  h(<exp(g,b(j)), <gA, IdI(i)> > ,skeyid)   >  >  > )

system ((!_j R: Responder(j)) | (!_i I: Initiator(i))).


goal wa_1 :
  forall (i,j:index),
    happens(I1(i,j)) =>
    cond@I1(i,j) <=>
    ( happens(R(j,i)) && R(j,i) < I1(i,j) &&

      fst(output@R(j,i)) = fst(input@I1(i,j)) &&
      fst(snd(output@R(j,i))) = fst(snd(input@I1(i,j))) &&
      fst(snd(snd(output@R(j,i)))) = fst(snd(snd(input@I1(i,j)))) &&
      snd(snd(snd(output@R(j,i)))) = snd(snd(snd(input@I1(i,j)))) &&

     fst(input@R(j,i)) = fst(output@I(i)) &&
     fst(snd(input@R(j,i))) = fst(snd(output@I(i))) &&
     snd(snd(input@R(j,i))) = snd(snd(output@I(i)))
     ).
Proof.
  intro i j.
  split.

  cycle 1.
  depends I(i), I1(i,j).
  expand cond.
  expandall.


help.
