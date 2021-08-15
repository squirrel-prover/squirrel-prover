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

name sk : message.

process Initiator(i:index) =
  out(cI, <exp(g,a(i)), < Ni(i), IdI(i) >>);

  in(cI, m);
  let gB = fst(m) in

  let RIdR = fst(snd(snd(m))) in
  let HashR = snd(snd(snd(m))) in
  (* find the preshared key in the database corresponding to the identity *)
  try find j such that RIdR = IdR(j) in
    if HashR =  h(<gB, < exp(g,a(i))  , IdR(j)> > , h(<Ni(i), fst(snd(m)) > ,psk(i,j))) then
       let finalkey = h( exp(gB,a(i)),  h(<Ni(i), fst(snd(m)) > ,psk(i,j))) in
       out(cI,  h(<exp(g,a(i)), <gB, IdI(i)> > , h(<Ni(i), fst(snd(m)) > ,psk(i,j)))  )

process Responder(j:index) =
  in(cI, m);
  let gA  = fst(m) in

  let RIdI = snd(snd(m)) in
  (* find the preshared key in the database corresponding to the identity *)
  try find i such that RIdI = IdI(i) in

    out(cR, <exp(g,b(j)), <Nr(j), < IdR(j)  ,  h(<exp(g,b(j)), <gA, IdR(j)> > , h(< fst(snd(m)),Nr(j) > ,psk(i,j)))   >  >  > );

    in(cR, m2);
    if m2 =  h(<gA, <exp(g,b(j)), IdI(i)> > , h(< fst(snd(m)),Nr(j) > ,psk(i,j))) then
       out(cR, diff(h(ok,sk),ko))



system [Main] ((!_j R: Responder(j)) | (!_i I: Initiator(i))).


name Ininr : index -> index ->  index -> index -> message

name IgarbI : index -> index ->  index -> index -> message
name IgarbR : index -> index ->  index -> index -> message


process InitiatorI(i:index) =
  out(cI, <exp(g,a(i)), < Ni(i), IdI(i) >>);

  in(cI, m);
  let gB = fst(m) in
  let RNr = fst(snd(m)) in
  let RIdR = fst(snd(snd(m))) in
  let HashR = snd(snd(snd(m))) in
  (* find the preshared key in the database corresponding to the identity *)
  try find j such that RIdR = IdR(j) in
    let skeyid =
         try find jl,il such that  <Ni(i),RNr > = <Ni(il),Nr(jl) > && il = i && jl=j in
              Ininr(jl,il,i,j)
             (* glob I psk:
                  Collect set of hashes h(m1,psk), h(m2,psk). (fail if more than two)
                  h(m1,sk) ->   if m1=m2 then nS else n1
                  h(m2,sk) ->   if m1=m2 then nS else n2
              *)
         else
             IgarbI(j,i,i,j)
 in
    if HashR =  h(<gB, < exp(g,a(i))  , IdR(j)> > ,skeyid) then
       let finalkey = h( exp(gB,a(i)), skeyid) in
       out(cI,  h(<exp(g,a(i)), <gB, IdI(i)> > ,skeyid)  ).

process ResponderI(j:index) =
  in(cI, m);
  let gA  = fst(m) in
  let RNi = fst(snd(m)) in
  let RIdI = snd(snd(m)) in
  (* find the preshared key in the database corresponding to the identity *)
  try find i such that RIdI = IdI(i) in
    let skeyid =
      try find jl, il such that <RNi,Nr(j) > = <Ni(il),Nr(jl) >  && il=i && jl=j in
          Ininr(jl,il,i,j)
      else
          IgarbR(j,i,i,j)

     in
    out(cR, <exp(g,b(j)), <Nr(j), < IdR(j)  ,  h(<exp(g,b(j)), <gA, IdR(j)> > ,skeyid)   >  >  > );

    in(cR, m2);
    if m2 =  h(<gA, <exp(g,b(j)), IdI(i)> > ,skeyid) then
       out(cR, ok)



system [Ideal1] ((!_j R: ResponderI(j)) | (!_i I: InitiatorI(i))).

axiom [Main] redseq : forall (m:message), seq(jl,il->m) = m.
axiom [Main] redseqnoj : forall (m:message), seq(jl,il->m) = seq(il->m).
axiom [Main] redseqnoi : forall (m:message), seq(jl,il->m) = seq(jl->m).
axiom [Main] redseqil : forall (i1:index), seq(jl,il->il=i1) = empty.
axiom [Main] redseqjl : forall (i1:index), seq(jl,il->jl=i1) = empty.

equiv [Main/left,Ideal1/right] test.
Proof.
print.
globalprf seq(il,jl->  h(<Ni(il), Nr(jl) > ,psk(il,jl))), news.
print.
globalprf seq(il2,jl2->  h(<Ni(il2), fst(snd(input@I1(il2,jl2))) > ,psk(il2,jl2))), newss.
print.
globalprf seq(il2,jl2->  h(<fst(snd(input@R(jl2,il2))),Nr(jl2) > ,psk(il2,jl2))), newss2.
print.

rename seq(i,j,k,l ->  n_PRF(i,j,k,l)), seq(i,j,k,l ->  Ininr(i,j,k,l)), tk.
rename seq(i,j,k,l ->  n_PRF1(i,j,k,l)), seq(i,j,k,l ->  IgarbI(i,j,k,l)), tk2.
rename seq(i,j,k,l ->  n_PRF2(i,j,k,l)), seq(i,j,k,l ->  IgarbR(i,j,k,l)), tk3.
print.

enrich seq(i-> b(i)). enrich seq(i-> a(i)). enrich seq(i-> IdI(i)).  enrich seq(i-> IdR(i)).  enrich seq(i-> Ni(i)).  enrich seq(i-> Nr(i)). enrich seq(i,j,k,l -> Ininr(i,j,k,l)). enrich seq(i,j,k,l -> IgarbI(i,j,k,l)). enrich seq(i,j,k,l -> IgarbR(i,j,k,l)).
induction t.

cycle 5.
expandall.

equivalent   try find jl,il such that
            (<Ni(i),fst(snd(input@I1(i,j)))> = <Ni(il),Nr(jl)> &&
             (il = i && jl = j))
          in Ininr(jl,il,i,j)
          else
            try find jl2,il2 such that
              (<Ni(i),fst(snd(input@I1(i,j)))> =
               <Ni(il2),fst(snd(input@I1(il2,jl2)))> && (il2 = i && jl2 = j))
            in IgarbI(jl2,il2,i,j)
            else
              try find jl2,il2 such that
                (<Ni(i),fst(snd(input@I1(i,j)))> =
                 <fst(snd(input@R(jl2,il2))),Nr(jl2)> && (il2 = i && jl2 = j))
              in IgarbR(jl2,il2,i,j)
              else h(<Ni(i),fst(snd(input@I1(i,j)))>,psk(i,j)),
  try find jl,il such that
            (<Ni(i),fst(snd(input@I1(i,j)))> = <Ni(il),Nr(jl)> &&
             (il = i && jl = j))
          in Ininr(jl,il,i,j)
          else
 IgarbI(j,i,i,j)
           .

fa.
case  (try find jl2,il2 such that
   (<Ni(i),fst(snd(input@I1(i,j)))> = <Ni(il2),fst(snd(input@I1(il2,jl2)))> &&
    (il2 = i && jl2 = j))
 in IgarbI(jl2,il2,i,j)
 else
   try find jl2,il2 such that
     (<Ni(i),fst(snd(input@I1(i,j)))> = <fst(snd(input@R(jl2,il2))),Nr(jl2)> &&
      (il2 = i && jl2 = j))
   in IgarbR(jl2,il2,i,j) else h(<Ni(i),fst(snd(input@I1(i,j)))>,psk(i,j))).
use H0 with j,i.

fa 9. fa 10. fa 10. fa 11. fa 10. fa 10. fa 10. fa 13.
equivalent diff(
     try find jl,il such that
       (<Ni(i),fst(snd(input@I1(i,j)))> = <Ni(il),Nr(jl)> &&
        (il = i && jl = j)) in Ininr(jl,il,i,j) else IgarbI(j,i,i,j),
     try find jl,il such that
       (<Ni(i),fst(snd(input@I1(i,j)))> = <Ni(il),Nr(jl)> && il = i && jl = j)
     in Ininr(jl,il,i,j) else IgarbI(j,i,i,j)),      try find jl,il such that
       (<Ni(i),fst(snd(input@I1(i,j)))> = <Ni(il),Nr(jl)> && il = i && jl = j)
     in Ininr(jl,il,i,j) else IgarbI(j,i,i,j).
project. fa. fa.

fa 10. fa 10. fa 10. fa 13. fa 13. fa 12. fa 12. repeat fa 12. fa 14.

(* TODO seqdup tactic *)


help.




name PRFninr : index -> index -> message

name PRFgarbI : index -> message
name PRFgarbR : index -> message

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
              PRFninr( i2, j2)
             (* glob PRF psk:
                  Collect set of hashes h(m1,psk), h(m2,psk). (fail if more than two)
                  h(m1,sk) ->   if m1=m2 then nS else n1
                  h(m2,sk) ->   if m1=m2 then nS else n2
              *)
         else
             PRFgarbI(i)
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
          PRFninr(i2,j2)
      else
          PRFgarbR(j)

     in
    out(cR, <exp(g,b(j)), <Nr(j), < IdR(j)  ,  h(<exp(g,b(j)), <gA, IdR(j)> > ,skeyid)   >  >  > );

    in(cR, m2);
    if m2 =  h(<gA, <exp(g,b(j)), IdI(i)> > ,skeyid) then
       out(cR, ok)



system [PRF] ((!_j R: ResponderPRF(j)) | (!_i I: InitiatorPRF(i))).




process InitiatorPRF2(i:index) =
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
              PRFninr( i2, j2)
         else
             PRFgarbI(i)
 in
    if HashR=
         try find i2,j2 such that  <Ni(i),RNr > = <Ni(i2),Nr(j2) > in
h(<gB, < exp(g,a(i))  , IdR(j)> > ,               PRFninr(i, j2))
         else
h(<gB, < exp(g,a(i))  , IdR(j)> > ,              PRFgarbI(i))

then
       let finalkey = h( exp(gB,a(i)), skeyid) in
       out(cI,
         try find i2,j2 such that  <Ni(i),RNr > = <Ni(i2),Nr(j2) > in
h(<exp(g,a(i)), <gB, IdI(i)> > ,               PRFninr(i, j2))
         else
h(<exp(g,a(i)), <gB, IdI(i)> > ,              PRFgarbI(i))


 )

process ResponderPRF2(j:index) =
  in(cI, m);
  let gA  = fst(m) in
  let RNi = fst(snd(m)) in
  let RIdI = snd(snd(m)) in
  (* find the preshared key in the database corresponding to the identity *)
  try find i such that RIdI = IdI(i) in
    let skeyid =
      try find i2, j2 such that <RNi,Nr(j) > = <Ni(i2),Nr(j2) > in
          PRFninr(i2,j2)
      else
          PRFgarbR(j)

     in
    out(cR, <exp(g,b(j)), <Nr(j), < IdR(j)  ,

      try find i2, j2 such that <RNi,Nr(j) > = <Ni(i2),Nr(j2) > in
h(<exp(g,b(j)), <gA, IdR(j)> > ,             PRFninr(i2,j))
      else
h(<exp(g,b(j)), <gA, IdR(j)> > ,             PRFgarbR(j))

>  >  > );

    in(cR, m2);
    if m2 =
     try find i2, j2 such that <RNi,Nr(j) > = <Ni(i2),Nr(j2) > in
     h(<gA, <exp(g,b(j)), IdI(i)> > ,          PRFninr(i2,j))
      else
     h(<gA, <exp(g,b(j)), IdI(i)> > ,          PRFgarbR(j))

 then
       out(cR, ok)



system [PRF2] ((!_j R: ResponderPRF2(j)) | (!_i I: InitiatorPRF2(i))).

goal [PRF2] fst_pair (x,y : message) : fst (<x, y >) = x.
Proof. auto. Qed.
hint rewrite fst_pair.
goal [PRF2] snd_pair (x,y : message) : snd (<x, y >) = y.
Proof. auto. Qed.
hint rewrite fst_pair.
(*
goal fst_pair (x,y : message) : fst (<x, seq(i -> y) >) = x.
Proof. auto. Qed.

goal fst_pair (x,y : message) : fst (<x, of_bool(forall i: index, y=x) >) = x.
Proof. auto. Qed.
goal fst_pair (x,y : message) : fst (<x,try find i such that y = IdI(i) in y else y>) = x.
Proof. auto. Qed.
*)


goal [PRF2] wa_1 :
  forall (i,j:index),
    happens(I1(i,j)) =>
    cond@I1(i,j) =>
    (exists (i0:index), happens(R(j,i0)) && R(j,i0) < I1(i,j) &&

      fst(output@R(j,i0)) = fst(input@I1(i,j)) &&
      fst(snd(output@R(j,i0))) = fst(snd(input@I1(i,j))) &&
      fst(snd(snd(output@R(j,i0)))) = fst(snd(snd(input@I1(i,j)))) &&
(*      snd(snd(snd(output@R(j,i0)))) = snd(snd(snd(input@I1(i,j)))) && *)

     fst(input@R(j,i0)) = fst(output@I(i))
(*     fst(snd(input@R(j,i0))) = fst(snd(output@I(i))) && -> we don't prove that the Ni are equal, cause we don't get with euf the key from the top. *)
(*     snd(snd(input@R(j,i0))) = snd(snd(output@I(i))) ->  *)
     ).
Proof.
 intro i j.

 expand cond.
 help.
 nosimpl(case  try find i2,j2 such that <Ni(i),RNr2(i)@I1(i,j)> = <Ni(i2),Nr(j2)>
     in h(<gB2(i)@I1(i,j),<exp(g,a(i)),IdR(j)>>,PRFninr(i,j2))
     else h(<gB2(i)@I1(i,j),<exp(g,a(i)),IdR(j)>>,PRFgarbI(i))).

 (* Case 1 -> honnest skeyid *)
 intro Ex.

substeq   (try find i2,j2 such that <Ni(i),RNr2(i)@I1(i,j)> = <Ni(i2),Nr(j2)>
       in h(<gB2(i)@I1(i,j),<exp(g,a(i)),IdR(j)>>,PRFninr(i,j2))
       else h(<gB2(i)@I1(i,j),<exp(g,a(i)),IdR(j)>>,PRFgarbI(i))),    h(<gB2(i)@I1(i,j),<exp(g,a(i)),IdR(j)>>,PRFninr(i,j2)); substeq  (try find i2,j3 such that <Ni(i),RNr2(i)@I1(i,j)> = <Ni(i2),Nr(j3)>
      in h(<gB2(i)@I1(i,j),<exp(g,a(i)),IdR(j)>>,PRFninr(i,j3))
      else h(<gB2(i)@I1(i,j),<exp(g,a(i)),IdR(j)>>,PRFgarbI(i))),
     h(<gB2(i)@I1(i,j),<exp(g,a(i)),IdR(j)>>,PRFninr(i,j2)).
 euf Meq.

exists i0.
expand output. repeat split.
expand gB2.
rewrite fst_pair.
rewrite snd_pair fst_pair.
rewrite snd_pair snd_pair fst_pair.

depends I(i), I1(i,j).
depends I(i), I1(i,j).
expand output.

 (* Case 2 -> dishonnest skeyid, trivial as no one else computes this key *)

substeq  (try find i2,j2 such that <Ni(i),RNr2(i)@I1(i,j)> = <Ni(i2),Nr(j2)>
       in h(<gB2(i)@I1(i,j),<exp(g,a(i)),IdR(j)>>,PRFninr(i,j2))
       else h(<gB2(i)@I1(i,j),<exp(g,a(i)),IdR(j)>>,PRFgarbI(i))),
      h(<gB2(i)@I1(i,j),<exp(g,a(i)),IdR(j)>>,PRFgarbI(i)).
 euf Meq.
Qed.

(*

goal [PRF2] was_1 :
  forall (i,j:index),
    happens(I1(i,j)) =>
    exec@I1(i,j) <=>
    exec@pred(I1(i,j)) &&
    (exists (i0:index), happens(R(j,i0)) && R(j,i0) < I1(i,j) &&

      fst(output@R(j,i0)) = fst(input@I1(i,j)) &&
      fst(snd(output@R(j,i0))) = fst(snd(input@I1(i,j))) &&
      fst(snd(snd(output@R(j,i0)))) = fst(snd(snd(input@I1(i,j)))) &&
      snd(snd(snd(output@R(j,i0)))) = snd(snd(snd(input@I1(i,j)))) &&

     fst(input@R(j,i0)) = fst(output@I(i))
(*     fst(snd(input@R(j,i0))) = fst(snd(output@I(i))) && -> we don't prove that the Ni are equal, cause we don't get with euf the key from the top. *)
(*     snd(snd(input@R(j,i0))) = snd(snd(output@I(i))) ->  *)
     ).
Proof.
 intro i j.

 split.
 expand exec.
 expand cond.
 help.
 nosimpl(case  try find i2,j2 such that <Ni(i),RNr2(i)@I1(i,j)> = <Ni(i2),Nr(j2)>
     in h(<gB2(i)@I1(i,j),<exp(g,a(i)),IdR(j)>>,PRFninr(i,j2))
     else h(<gB2(i)@I1(i,j),<exp(g,a(i)),IdR(j)>>,PRFgarbI(i))).

 (* Case 1 -> honnest skeyid *)
 intro Ex.

substeq   (try find i2,j2 such that <Ni(i),RNr2(i)@I1(i,j)> = <Ni(i2),Nr(j2)>
       in h(<gB2(i)@I1(i,j),<exp(g,a(i)),IdR(j)>>,PRFninr(i,j2))
       else h(<gB2(i)@I1(i,j),<exp(g,a(i)),IdR(j)>>,PRFgarbI(i))),    h(<gB2(i)@I1(i,j),<exp(g,a(i)),IdR(j)>>,PRFninr(i,j2)); substeq  (try find i2,j3 such that <Ni(i),RNr2(i)@I1(i,j)> = <Ni(i2),Nr(j3)>
      in h(<gB2(i)@I1(i,j),<exp(g,a(i)),IdR(j)>>,PRFninr(i,j3))
      else h(<gB2(i)@I1(i,j),<exp(g,a(i)),IdR(j)>>,PRFgarbI(i))),
     h(<gB2(i)@I1(i,j),<exp(g,a(i)),IdR(j)>>,PRFninr(i,j2)).
 euf Meq.

exists i0.
expand output. repeat split.
expand gB2.
rewrite fst_pair.
rewrite snd_pair fst_pair.
rewrite snd_pair snd_pair fst_pair.

depends I(i), I1(i,j).
depends I(i), I1(i,j).

rewrite snd_pair snd_pair snd_pair.


case (try find i2,j2 such that <RNi2(j)@R(j,i0),Nr(j)> = <Ni(i2),Nr(j2)>
 in h(<exp(g,b(j)),<gA2(j)@R(j,i0),IdR(j)>>,PRFninr(i2,j))
 else h(<exp(g,b(j)),<gA2(j)@R(j,i0),IdR(j)>>,PRFgarbR(j))) .

substeq  (try find i2,j2 such that <RNi2(j)@R(j,i0),Nr(j)> = <Ni(i2),Nr(j2)>
       in h(<exp(g,b(j)),<gA2(j)@R(j,i0),IdR(j)>>,PRFninr(i2,j))
       else h(<exp(g,b(j)),<gA2(j)@R(j,i0),IdR(j)>>,PRFgarbR(j))),
      h(<exp(g,b(j)),<gA2(j)@R(j,i0),IdR(j)>>,PRFninr(i2,j)).
substeq  (try find i3,j2 such that <RNi2(j)@R(j,i0),Nr(j)> = <Ni(i3),Nr(j2)>
       in h(<exp(g,b(j)),<gA2(j)@R(j,i0),IdR(j)>>,PRFninr(i3,j))
       else h(<exp(g,b(j)),<gA2(j)@R(j,i0),IdR(j)>>,PRFgarbR(j))),
      h(<exp(g,b(j)),<gA2(j)@R(j,i0),IdR(j)>>,PRFninr(i2,j)).


(*expand output.

 (* Case 2 -> dishonnest skeyid, trivial as no one else computes this key *)

substeq  (try find i2,j2 such that <Ni(i),RNr2(i)@I1(i,j)> = <Ni(i2),Nr(j2)>
       in h(<gB2(i)@I1(i,j),<exp(g,a(i)),IdR(j)>>,PRFninr(i,j2))
       else h(<gB2(i)@I1(i,j),<exp(g,a(i)),IdR(j)>>,PRFgarbI(i))),
      h(<gB2(i)@I1(i,j),<exp(g,a(i)),IdR(j)>>,PRFgarbI(i)).
 euf Meq.


expand exec.
expand cond.
*)
cycle 3.
expandall.
rewrite snd_pair snd_pair snd_pair in Meq0.
rewrite snd_pair snd_pair fst_pair in Meq1.
rewrite snd_pair fst_pair in Meq2.
rewrite fst_pair in Meq3.



Qed.

*)



goal [PRF2] wa_2 :
  forall (i,j:index),
    happens(R1(j,i)) =>
    exec@R1(j,i) =>
  exists j0:index,
  fst(input@R(j,i)) = fst(output@I(i)) &&
    fst(snd(input@R(j,i))) = fst(snd(output@I(i))) &&
   snd(snd(input@R(j,i))) = snd(snd(output@I(i))).

Proof.
 intro i j.
expand exec.
 expand cond.
 case    try find i2,j2 such that <RNi2(j)@R1(j,i),Nr(j)> = <Ni(i2),Nr(j2)>
   in h(<gA2(j)@R1(j,i),<exp(g,b(j)),IdI(i)>>,PRFninr(i2,j))
   else h(<gA2(j)@R1(j,i),<exp(g,b(j)),IdI(i)>>,PRFgarbR(j)).
 substeq  (try find i2,j2 such that <RNi2(j)@R1(j,i),Nr(j)> = <Ni(i2),Nr(j2)>
       in h(<gA2(j)@R1(j,i),<exp(g,b(j)),IdI(i)>>,PRFninr(i2,j))
       else h(<gA2(j)@R1(j,i),<exp(g,b(j)),IdI(i)>>,PRFgarbR(j))),
      h(<gA2(j)@R1(j,i),<exp(g,b(j)),IdI(i)>>,PRFninr(i2,j)).
substeq  (try find i3,j2 such that <RNi2(j)@R1(j,i),Nr(j)> = <Ni(i3),Nr(j2)>
       in h(<gA2(j)@R1(j,i),<exp(g,b(j)),IdI(i)>>,PRFninr(i3,j))
       else h(<gA2(j)@R1(j,i),<exp(g,b(j)),IdI(i)>>,PRFgarbR(j))),
      h(<gA2(j)@R1(j,i),<exp(g,b(j)),IdI(i)>>,PRFninr(i2,j)).

  (* honest case *)
  euf H0.
  exists i.
  depends I(i), I1(i,j0).
  case H1.

  executable pred(R1(j,i)).
  depends R(j,i), R1(j,i).
  use H2 with R(j,i).
  expand exec. expand cond.

 (* dishonest case *)
 substeq (try find i2,j2 such that <RNi2(j)@R1(j,i),Nr(j)> = <Ni(i2),Nr(j2)>
      in h(<gA2(j)@R1(j,i),<exp(g,b(j)),IdI(i)>>,PRFninr(i2,j))
      else h(<gA2(j)@R1(j,i),<exp(g,b(j)),IdI(i)>>,PRFgarbR(j))),
     h(<gA2(j)@R1(j,i),<exp(g,b(j)),IdI(i)>>,PRFgarbR(j)).
 euf H0.
Qed.



(* ROR *)
name idealkey : index -> message

process InitiatorPRFROR(i:index) =
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
              PRFninr( i2, j2)
         else
             PRFgarbI(i)
 in
    if HashR=
         try find i2,j2 such that  <Ni(i),RNr > = <Ni(i2),Nr(j2) > in
h(<gB, < exp(g,a(i))  , IdR(j)> > ,               PRFninr(i, j2))
         else
h(<gB, < exp(g,a(i))  , IdR(j)> > ,              PRFgarbI(i))

then
       out(cI,
         try find i2,j2 such that  <Ni(i),RNr > = <Ni(i2),Nr(j2) > in
h(<exp(g,a(i)), <gB, IdI(i)> > ,               PRFninr(i, j2))
         else
h(<exp(g,a(i)), <gB, IdI(i)> > ,              PRFgarbI(i))


 );
       let finalkey =
   try find i2,j2 such that  <Ni(i),RNr > = <Ni(i2),Nr(j2) > in
h( exp(gB,a(i)),             PRFninr(i, j2))
         else
h( exp(gB,a(i)),            PRFgarbI(i))


in

out(cI, diff(finalkey,idealkey(i))).


process ResponderPRFROR(j:index) =
  in(cI, m);
  let gA  = fst(m) in
  let RNi = fst(snd(m)) in
  let RIdI = snd(snd(m)) in
  (* find the preshared key in the database corresponding to the identity *)
  try find i such that RIdI = IdI(i) in
    let skeyid =
      try find i2, j2 such that <RNi,Nr(j) > = <Ni(i2),Nr(j2) > in
          PRFninr(i2,j2)
      else
          PRFgarbR(j)

     in
    out(cR, <exp(g,b(j)), <Nr(j), < IdR(j)  ,

      try find i2, j2 such that <RNi,Nr(j) > = <Ni(i2),Nr(j2) > in
h(<exp(g,b(j)), <gA, IdR(j)> > ,             PRFninr(i2,j))
      else
h(<exp(g,b(j)), <gA, IdR(j)> > ,             PRFgarbR(j))

>  >  > );

    in(cR, m2);
    if m2 =
     try find i2, j2 such that <RNi,Nr(j) > = <Ni(i2),Nr(j2) > in
     h(<gA, <exp(g,b(j)), IdI(i)> > ,          PRFninr(i2,j))
      else
     h(<gA, <exp(g,b(j)), IdI(i)> > ,          PRFgarbR(j))

 then
      let finalkey =
     try find i2, j2 such that <RNi,Nr(j) > = <Ni(i2),Nr(j2) > in
 h( exp(gA,b(j)),                PRFninr(i2,j))
      else
 h( exp(gA,b(j)),                PRFgarbR(j))

in
  out(cR, diff(finalkey,idealkey(i))).


(*
another call to PRF glob, with the message this time.

So, the tactic we want is:

globalprf h(m,sk):
   all hashes h(x,sk) --> if x =m then n else h(x,sk).


uniqprf h(m[vi],sk):
  collect set of other hashes h(x_i,sk). If
    1) all i x_i <> m;
    2)  vi <> vj => m[vi] <> m[vj]


globalprf psk:
      Collect set of hashes h(m1,psk), h(m2,psk). (fail if more than two)
        h(m1,sk) ->   if m1=m2 then nS else n1
        h(m2,sk) ->   if m1=m2 then nS else n2


 *)
