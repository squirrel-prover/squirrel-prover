(*******************************************************************************

Internet Key Exchange (IKE) Version 1, with Pre-Shared Key.

Defined in RFC2409 -> https://datatracker.ietf.org/doc/html/rfc2409

Claimed to be Post-Quantum secure in https://datatracker.ietf.org/doc/html/rfc8784


# Protocol Description

We consider the phase 1 of the aggressive mode.

Each pairing as a pre-shared key, psk.

(CKY = cookie)

The key exchange is given as

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

(* set postQuantumSound = true. *)

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
    if HashR =  h(<gB, < exp(g,a(i))  , IdR(j)> > ,skeyid) then
       let finalkey = h( exp(gB,a(i)), skeyid) in
       out(cI,  h(<exp(g,a(i)), <gB, IdI(i)> > ,skeyid)  )

process Responder(j:index) =
  in(cI, m);
  let gA  = fst(m) in
  let RNi = fst(snd(m)) in
  let RIdI = snd(snd(m)) in
  (* find the preshared key in the database corresponding to the identity *)
  try find i such that RIdI = IdI(i) in
    let skeyid = h(<RNi,Nr(j) > ,psk(i,j)) in
    out(cR, <exp(g,b(j)), <Nr(j), < IdR(j)  ,  h(<exp(g,b(j)), <gA, IdR(j)> > ,skeyid)   >  >  > );

    in(cR, m2);
    if m2 =  h(<gA, <exp(g,b(j)), IdI(i)> > ,skeyid) then
       out(cR, ok)



system ((!_j R: Responder(j)) | (!_i I: Initiator(i))).



name PRFninr : index -> index -> index -> index -> message

name PRFgarbI : index -> message
name PRFgarbR : index ->index -> message

process InitiatorPRF(i:index) =
  out(cI, <exp(g,a(i)), < Ni(i), IdI(i) >>);

  in(cI, m);
  let gB = fst(m) in
  let RNr = fst(snd(m)) in
  let RIdR = fst(snd(snd(m))) in
  let HashR = snd(snd(snd(m))) in
  (* find the preshared key in the database corresponding to the identity *)
  try find j such that RIdR = IdR(j) in
    let skeyid =
         try find i2,j2 such that  <Ni(i),RNr > = <Ni(i2),Nr(j2) > in
              PRFninr(i,j, i2, j2)
         else
           diff(h(<Ni(i),RNr > ,psk(i,j)), PRFgarbI(i))
 in
    if HashR =  h(<gB, < exp(g,a(i))  , IdR(j)> > ,skeyid) then
       let finalkey = h( exp(gB,a(i)), skeyid) in
       out(cI,  h(<exp(g,a(i)), <gB, IdI(i)> > ,skeyid)  )

process ResponderPRF(j:index) =
  in(cI, m);
  let gA  = fst(m) in
  let RNi = fst(snd(m)) in
  let RIdI = snd(snd(m)) in
  (* find the preshared key in the database corresponding to the identity *)
  try find i such that RIdI = IdI(i) in
    let skeyid =
      try find i2, j2 such that <RNi,Nr(j) > = <Ni(i2),Nr(j2) > in
          PRFninr(i,j,i2,j2)
      else
        diff(h(<RNi,Nr(j) > ,psk(i,j)), PRFgarbR(j,i))

     in
    out(cR, <exp(g,b(j)), <Nr(j), < IdR(j)  ,  h(<exp(g,b(j)), <gA, IdR(j)> > ,skeyid)   >  >  > );

    in(cR, m2);
    if m2 =  h(<gA, <exp(g,b(j)), IdI(i)> > ,skeyid) then
       out(cR, ok)



system [PRF] ((!_j R: ResponderPRF(j)) | (!_i I: InitiatorPRF(i))).

equiv [PRF] keyusable.
Proof.
 enrich seq(i->Ni(i));  enrich seq(i->Nr(i));  enrich seq(i->IdI(i));  enrich seq(i->IdR(i));  enrich seq(i->a(i));  enrich seq(i->b(i)).
 induction t.
 expandall.
 fa 6.
 fa 7.
 fa 8.
fa 8.
 fa 9.
 fa 10.



 fa 11.
(* this step not PQ sound *)
 prf 11, h(<fst(snd(input@R(j,i))),Nr(j)>,psk(i,j)).

 yesif 11.
 project.
 repeat split.
 case H0.
 case H0.
 depends R(j,i), R1(j,i).
 depends R(j,i), R1(j,i).
 case H0.
 depends R(j,i), R2(j,i).
 depends R(j,i), R2(j,i).

 notleft H1.
 use H1 with i, j.
 notleft H1.
 use H1 with i, j.
 notleft H1.
 use H1 with i, j.


 fa 11.
 fresh 13.

 yesif 13.
 TBC


(*

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
*)
