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

name sk : message.

(***********************************)
(* Main expression of the protocol *)

process Initiator(i:index) =
  out(cI, <exp(g,a(i)), < Ni(i), IdI(i) >>);

  in(cI, m);
  (* find the preshared key in the database corresponding to the identity *)
  try find j such that fst(snd(snd(m)))(*RIdR*) = IdR(j) in
    if  snd(snd(snd(m)))(*HashR*) =  h(<  fst(m)(*gB*), < exp(g,a(i))  , IdR(j)> > , h(<Ni(i), fst(snd(m))(*Nr*) > ,psk(i,j))) then
       let finalkey = h( exp( fst(m)(*gB*) ,a(i)),  h(<Ni(i), fst(snd(m)) > ,psk(i,j))) in
       out(cI,  h(<exp(g,a(i)), < fst(m)(*gB*) , IdI(i)> > , h(<Ni(i), fst(snd(m))(*Nr*) > ,psk(i,j)))  )

process Responder(j:index) =
  in(cI, m);
  (* find the preshared key in the database corresponding to the identity *)
  try find i such that snd(snd(m))(*RIdi*) = IdI(i) in
    out(cR, <exp(g,b(j)), <Nr(j), < IdR(j)  ,  h(<exp(g,b(j)), <fst(m)(*gA*), IdR(j)> > , h(< fst(snd(m)),Nr(j) > ,psk(i,j)))   >  >  > );

    in(cR, m2);
    if m2 =  h(<fst(m)(*gA*), <exp(g,b(j)), IdI(i)> > , h(< fst(snd(m)),Nr(j) > ,psk(i,j))) then
       out(cR, ok)

system [Main] ((!_j R: Responder(j)) | (!_i I: Initiator(i))).


(***********************************)
(*       Idealized version 1       *)

(* The keys obtained with the first prf application are all randoms. Some are
honest and shared by the two parties, and some correspond to garbage keys. *)

name Ininr : index -> index  -> message
name IgarbI : index -> index -> message
name IgarbR : index -> index -> message

process InitiatorI(i:index) =
  out(cI, <exp(g,a(i)), < Ni(i), IdI(i) >>);

  in(cI, m);
  (* find the preshared key in the database corresponding to the identity *)
  try find j such that fst(snd(snd(m)))(*RIdR*) = IdR(j) in
    if  snd(snd(snd(m)))(*HashR*) =  h(<  fst(m)(*gB*), < exp(g,a(i))  , IdR(j)> > ,
        (* idealized key computation *)
        try find jl, il such that   (<Ni(i),fst(snd(m))(*Nr*)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
             Ininr(j,i)
        else
             IgarbI(j,i)
          ) then
       let finalkey = h( exp( fst(m)(*gB*) ,a(i)),
        (* idealized key computation *)
        try find jl, il such that   (<Ni(i),fst(snd(m))(*Nr*)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
             Ininr(j,i)
        else
             IgarbI(j,i)
       ) in
       out(cI,  h(<exp(g,a(i)), < fst(m)(*gB*) , IdI(i)> > ,
        (* idealized key computation *)
        try find jl, il such that   (<Ni(i),fst(snd(m))(*Nr*)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
             Ininr(j,i)
        else
             IgarbI(j,i)
)  )


process ResponderI(j:index) =
  in(cI, m);
  (* find the preshared key in the database corresponding to the identity *)
  try find i such that snd(snd(m))(*RIdi*) = IdI(i) in
    out(cR, <exp(g,b(j)), <Nr(j), < IdR(j)  ,  h(<exp(g,b(j)), <fst(m)(*gA*), IdR(j)> > ,
        (* idealized key computation *)
        try find jl, il such that   (< fst(snd(m)),Nr(j)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
             Ininr(j,i)
        else
             IgarbR(j,i)
        )   >  >  > );

    in(cR, m2);
    if m2 =  h(<fst(m)(*gA*), <exp(g,b(j)), IdI(i)> > ,
        (* idealized key computation *)
        try find jl, il such that   (< fst(snd(m)),Nr(j)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
             Ininr(j,i)
        else
             IgarbR(j,i)
        ) then
       out(cR, ok)

system [Ideal1] ((!_j R: ResponderI(j)) | (!_i I: InitiatorI(i))).

axiom [Main] tryfind : forall (i,j:index), input@I1(i,j) = input@I2(i,j).
(* We prove that the main expression and the ideal 1 are equivalent. *)
equiv [Main/left,Ideal1/right] test.
Proof.
print.
globalprf seq(il,jl->  h(<Ni(il), Nr(jl) > ,psk(il,jl))), news.
print.
globalprf seq(il2,jl2->  h(<Ni(il2), fst(snd(input@I1(il2,jl2))) > ,psk(il2,jl2))), newss.
print.
globalprf seq(il3,jl3->  h(<fst(snd(input@R(jl3,il3))),Nr(jl3) > ,psk(il3,jl3))), newss2.
print.

rename seq(i,j ->  n_PRF(i,j)), seq(i,j ->  Ininr(i,j)), tk.
rename seq(i,j ->  n_PRF1(i,j)), seq(i,j ->  IgarbI(i,j)), tk2.
rename seq(i,j ->  n_PRF2(i,j)), seq(i,j ->  IgarbR(i,j)), tk3.
print.

diffeq.
(* From here, we need to prove that we indede get ideal keys everywhere. Mostly dumb manipulations of all the conditions introduced by the prf tactic, that are all contractory.
TODO : need a better way to refer to the try find. Copy-pasting is dumb.
 *)
notleft H0.
case (try find jl2,il2 such that
   (<Ni(i),fst(snd(input@I2(i,j)))> = <Ni(il2),fst(snd(input@I1(il2,jl2)))> &&
    (il2 = i && jl2 = j))
 in IgarbI(jl2,il2)
 else
   try find jl3,il3 such that
     (<Ni(i),fst(snd(input@I2(i,j)))> = <fst(snd(input@R(jl3,il3))),Nr(jl3)> &&
      (il3 = i && jl3 = j))
   in IgarbR(jl3,il3) else h(<Ni(i),fst(snd(input@I2(i,j)))>,psk(i,j))).
use H4 with j,i.
by forceuse tryfind with i,j.

case (try find jl2,il2 such that
   (<Ni(i),fst(snd(input@I1(i,j)))> = <Ni(il2),fst(snd(input@I1(il2,jl2)))> &&
    (il2 = i && jl2 = j))
 in IgarbI(jl2,il2)
 else
   try find jl3,il3 such that
     (<Ni(i),fst(snd(input@I1(i,j)))> = <fst(snd(input@R(jl3,il3))),Nr(jl3)> &&
      (il3 = i && jl3 = j))
   in IgarbR(jl3,il3) else h(<Ni(i),fst(snd(input@I1(i,j)))>,psk(i,j))).
by use H4 with j,i.

case (try find jl2,il2 such that
   (<Ni(i),fst(snd(input@I1(i,j)))> = <Ni(il2),fst(snd(input@I1(il2,jl2)))> &&
    (il2 = i && jl2 = j))
 in IgarbI(jl2,il2)
 else
   try find jl3,il3 such that
     (<Ni(i),fst(snd(input@I1(i,j)))> = <fst(snd(input@R(jl3,il3))),Nr(jl3)> &&
      (il3 = i && jl3 = j))
   in IgarbR(jl3,il3) else h(<Ni(i),fst(snd(input@I1(i,j)))>,psk(i,j))).
by use H4 with j,i.

case (try find jl2,il2 such that
   (<fst(snd(input@R(j,i))),Nr(j)> = <Ni(il2),fst(snd(input@I1(il2,jl2)))> &&
    (il2 = i && jl2 = j))
 in IgarbI(jl2,il2)
 else
   try find jl3,il3 such that
     (<fst(snd(input@R(j,i))),Nr(j)> = <fst(snd(input@R(jl3,il3))),Nr(jl3)> &&
      (il3 = i && jl3 = j))
   in IgarbR(jl3,il3) else h(<fst(snd(input@R(j,i))),Nr(j)>,psk(i,j))).
notleft H0. use H0 with j,i.
by case H5.

case (try find jl3,il3 such that
   (<fst(snd(input@R(j,i))),Nr(j)> = <fst(snd(input@R(jl3,il3))),Nr(jl3)> &&
    (il3 = i && jl3 = j))
 in IgarbR(jl3,il3) else h(<fst(snd(input@R(j,i))),Nr(j)>,psk(i,j))).
by use H6 with j,i.


case try find jl,il such that
  (<fst(snd(input@R(j,i))),Nr(j)> = <Ni(il),Nr(jl)> && (il = i && jl = j))
in Ininr(jl,il)
else
  try find jl2,il2 such that
    (<fst(snd(input@R(j,i))),Nr(j)> = <Ni(il2),fst(snd(input@I1(il2,jl2)))> &&
     (il2 = i && jl2 = j))
  in IgarbI(jl2,il2)
  else
    try find jl3,il3 such that
      (<fst(snd(input@R(j,i))),Nr(j)> = <fst(snd(input@R(jl3,il3))),Nr(jl3)> &&
       (il3 = i && jl3 = j))
    in IgarbR(jl3,il3) else h(<fst(snd(input@R(j,i))),Nr(j)>,psk(i,j)).
case try find jl0,il0 such that
  (<fst(snd(input@R(jl,il))),Nr(jl)> = <Ni(il0),Nr(jl0)> &&
   (il0 = il && jl0 = jl)) in Ininr(jl,il) else IgarbR(jl,il).
substeq Meq.
substeq Meq1.
by use H4 with jl,il.

substeq Meq.
case try find jl2,il2 such that
  (<fst(snd(input@R(j,i))),Nr(j)> = <Ni(il2),fst(snd(input@I1(il2,jl2)))> &&
   (il2 = i && jl2 = j))
in IgarbI(jl2,il2)
else
  try find jl3,il3 such that
    (<fst(snd(input@R(j,i))),Nr(j)> = <fst(snd(input@R(jl3,il3))),Nr(jl3)> &&
     (il3 = i && jl3 = j))
  in IgarbR(jl3,il3) else h(<fst(snd(input@R(j,i))),Nr(j)>,psk(i,j)).
by use H4 with j,i.

case try find jl3,il3 such that
  (<fst(snd(input@R(j,i))),Nr(j)> = <fst(snd(input@R(jl3,il3))),Nr(jl3)> &&
   (il3 = i && jl3 = j))
in IgarbR(jl3,il3) else h(<fst(snd(input@R(j,i))),Nr(j)>,psk(i,j)).
substeq Meq.

case try find jl,il such that
  (<fst(snd(input@R(j,i))),Nr(j)> = <Ni(il),Nr(jl)> && (il = i && jl = j))
in Ininr(j,i) else IgarbR(j,i).
substeq Meq.
by use H4 with jl,il.

by substeq Meq1.
by use H6 with j,i.

case (try find jl2,il2 such that
   (<fst(snd(input@R(j,i))),Nr(j)> = <Ni(il2),fst(snd(input@I1(il2,jl2)))> &&
    (il2 = i && jl2 = j))
 in IgarbI(jl2,il2)
 else
   try find jl3,il3 such that
     (<fst(snd(input@R(j,i))),Nr(j)> = <fst(snd(input@R(jl3,il3))),Nr(jl3)> &&
      (il3 = i && jl3 = j))
   in IgarbR(jl3,il3) else h(<fst(snd(input@R(j,i))),Nr(j)>,psk(i,j))).
notleft H0. use H0 with j,i. by case H4.

case (try find jl3,il3 such that
   (<fst(snd(input@R(j,i))),Nr(j)> = <fst(snd(input@R(jl3,il3))),Nr(jl3)> &&
    (il3 = i && jl3 = j))
 in IgarbR(jl3,il3) else h(<fst(snd(input@R(j,i))),Nr(j)>,psk(i,j))).
use H5 with j,i.
Qed.

(***********************************)
(*       Idealized version 2       *)

(* In this next game, we just push one level up the tryfinds, with a syntactic manipulation. *)

process InitiatorI2(i:index) =
  out(cI, <exp(g,a(i)), < Ni(i), IdI(i) >>);

  in(cI, m);
  (* find the preshared key in the database corresponding to the identity *)
  try find j such that fst(snd(snd(m)))(*RIdR*) = IdR(j) in
    if  snd(snd(snd(m)))(*HashR*) =
        (* idealized key computation *)
        try find jl, il such that   (<Ni(i),fst(snd(m))(*Nr*)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
         h(<  fst(m)(*gB*), < exp(g,a(i))  , IdR(j)> > ,    Ininr(j,i))
        else
           h(<  fst(m)(*gB*), < exp(g,a(i))  , IdR(j)> > ,  IgarbI(j,i))
           then
       out(cI,
        (* idealized key computation *)
        try find jl, il such that   (<Ni(i),fst(snd(m))(*Nr*)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
             h(<exp(g,a(i)), < fst(m)(*gB*) , IdI(i)> > ,Ininr(j,i))
        else
            h(<exp(g,a(i)), < fst(m)(*gB*) , IdI(i)> > , IgarbI(j,i))
)


process ResponderI2(j:index) =
  in(cI, m);
  (* find the preshared key in the database corresponding to the identity *)
  try find i such that snd(snd(m))(*RIdi*) = IdI(i) in
    out(cR, <exp(g,b(j)), <Nr(j), < IdR(j)  ,
        (* idealized key computation *)
        try find jl, il such that   (< fst(snd(m)),Nr(j)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
            h(<exp(g,b(j)), <fst(m)(*gA*), IdR(j)> > ,   Ininr(j,i))
        else
          h(<exp(g,b(j)), <fst(m)(*gA*), IdR(j)> > ,     IgarbR(j,i))
           >  >  > );

    in(cR, m2);
    if m2 =
        (* idealized key computation *)
        try find jl, il such that   (< fst(snd(m)),Nr(j)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
            h(<fst(m)(*gA*), <exp(g,b(j)), IdI(i)> > ,  Ininr(j,i))
        else
            h(<fst(m)(*gA*), <exp(g,b(j)), IdI(i)> > ,  IgarbR(j,i))
         then
       out(cR, ok)

system [Ideal2] ((!_j R: ResponderI2(j)) | (!_i I: InitiatorI2(i))).

(* We now prove the authentication on this ideal system. *)
goal [Ideal2] fst_pair (x,y : message) : fst (<x, y >) = x.
Proof. auto. Qed.
hint rewrite fst_pair.
goal [Ideal2] snd_pair (x,y : message) : snd (<x, y >) = y.
Proof. auto. Qed.
hint rewrite fst_pair.

goal [Ideal2] wa_1 :
  forall (i,j:index),
    happens(I1(i,j)) =>
    cond@I1(i,j) =>
    (exists (i0:index), happens(R(j,i0)) && R(j,i0) < I1(i,j) &&

      fst(output@R(j,i0)) = fst(input@I1(i,j)) &&
      fst(snd(output@R(j,i0))) = fst(snd(input@I1(i,j))) &&
      fst(snd(snd(output@R(j,i0)))) = fst(snd(snd(input@I1(i,j)))) &&
     fst(input@R(j,i0)) = fst(output@I(i))
     ).
Proof.
 intro i j.

 expand cond.

case  try find jl,il such that
       (<Ni(i),fst(snd(input@I1(i,j)))> = <Ni(il),Nr(jl)> &&
        (il = i && jl = j))
     in h(<fst(input@I1(i,j)),<exp(g,a(i)),IdR(j)>>,Ininr(j,i))
     else h(<fst(input@I1(i,j)),<exp(g,a(i)),IdR(j)>>,IgarbI(j,i)).

 (* Case 1 -> honnest skeyid *)
substeq Meq1.
euf Meq.

exists il.
expand output. repeat split.
by rewrite fst_pair.
by rewrite snd_pair fst_pair.
by rewrite snd_pair snd_pair fst_pair.
by depends I(il), I1(il,jl).

 (* Case 2 -> dishonnest skeyid, trivial as no one else computes this key *)
substeq Meq1.
euf Meq.
Qed.

goal [Ideal2] wa_2 :
  forall (i,j:index),
    happens(R1(j,i)) =>
    exec@R1(j,i) =>
     happens(I(i)) &&
  fst(input@R(j,i)) = fst(output@I(i)) &&
    fst(snd(input@R(j,i))) = fst(snd(output@I(i))) &&
   snd(snd(input@R(j,i))) = snd(snd(output@I(i))).

Proof.
 intro i j.
expand exec.
 expand cond.

case  try find jl,il such that
      (<fst(snd(input@R(j,i))),Nr(j)> = <Ni(il),Nr(jl)> && (il = i && jl = j))
    in h(<fst(input@R(j,i)),<exp(g,b(j)),IdI(i)>>,Ininr(j,i))
    else h(<fst(input@R(j,i)),<exp(g,b(j)),IdI(i)>>,IgarbR(j,i)).
substeq Meq.

  (* honest case *)
  euf H0.

  depends I(il), I1(il,jl).
  by case H1.

  executable pred(R1(jl,il)).
  depends R(jl,il), R1(jl,il).
  use H2 with R(jl,il).
  expand exec. expand cond.

substeq Meq.
 euf H0.
Qed.


(*********************************)
(* Final game for Real or Random *)

(* this is ideal 2, where in addition each party IdI(i) in the end either outputs the derived key, or an idealied key ideal(i,j) if it thinks it is talking to party IdR(j). *)

name idealkeys : index -> index -> message

process InitiatorRoR(i:index) =
  out(cI, <exp(g,a(i)), < Ni(i), IdI(i) >>);

  in(cI, m);
  (* find the preshared key in the database corresponding to the identity *)
  try find j such that fst(snd(snd(m)))(*RIdR*) = IdR(j) in
    if  snd(snd(snd(m)))(*HashR*) =
        (* idealized key computation *)
        try find jl, il such that   (<Ni(i),fst(snd(m))(*Nr*)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
         h(<  fst(m)(*gB*), < exp(g,a(i))  , IdR(j)> > ,    Ininr(j,i))
        else
           h(<  fst(m)(*gB*), < exp(g,a(i))  , IdR(j)> > ,  IgarbI(j,i))
           then
       out(cI,
        (* idealized key computation *)
        try find jl, il such that   (<Ni(i),fst(snd(m))(*Nr*)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
             h(<exp(g,a(i)), < fst(m)(*gB*) , IdI(i)> > ,Ininr(j,i))
        else
            h(<exp(g,a(i)), < fst(m)(*gB*) , IdI(i)> > , IgarbI(j,i)));

       out(cI,diff(      try find jl, il such that   (<Ni(i),fst(snd(m))(*Nr*)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
             h( exp(fst(m),a(i)), Ininr(j,i))
        else
             h( exp(fst(m),a(i)),  IgarbI(j,i)), idealkeys(j,i))).


process ResponderRoR(j:index) =
  in(cI, m);
  (* find the preshared key in the database corresponding to the identity *)
  try find i such that snd(snd(m))(*RIdi*) = IdI(i) in
    out(cR, <exp(g,b(j)), <Nr(j), < IdR(j)  ,
        (* idealized key computation *)
        try find jl, il such that   (< fst(snd(m)),Nr(j)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
            h(<exp(g,b(j)), <fst(m)(*gA*), IdR(j)> > ,   Ininr(j,i))
        else
          h(<exp(g,b(j)), <fst(m)(*gA*), IdR(j)> > ,     IgarbR(j,i))
           >  >  > );

    in(cR, m2);
    if m2 =
        (* idealized key computation *)
        try find jl, il such that   (< fst(snd(m)),Nr(j)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
            h(<fst(m)(*gA*), <exp(g,b(j)), IdI(i)> > ,  Ininr(j,i))
        else
            h(<fst(m)(*gA*), <exp(g,b(j)), IdI(i)> > ,  IgarbR(j,i))
         then
       out(cR,diff(
        try find jl, il such that   (< fst(snd(m)),Nr(j)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
              h( exp(fst(m),b(j)), Ininr(j,i))
        else
               h( exp(fst(m),b(j)),  IgarbR(j,i))
, idealkeys(j,i))).

system [Ror] ((!_j R: ResponderRoR(j)) | (!_i I: InitiatorRoR(i))).


axiom [Ror] ddhcommu : forall (i,j:index), exp(exp(g,a(i)),b(j)) =  exp(exp(g,b(j)),a(i)) .
axiom [Ror] ddhnotuple : forall (m1,m2,m3,m4:message), exp(m3,m4) <> <m1,m2>.

(* we first prove two small authentication lemmas, so that if we reach the ideal key computation, we now we have the correct parameters. *)

goal [Ror] helper_wa :
  forall (i,j:index),
    happens(R1(j,i)) =>
    exec@R1(j,i) =>
    fst(snd(input@R(j,i))) = Ni(i) &&
    fst(input@R(j,i)) = exp(g,a(i))
.

Proof.
 intro i j.
 expand exec.
 expand cond.
 case try find jl,il such that
      (<fst(snd(input@R(j,i))),Nr(j)> = <Ni(il),Nr(jl)> && (il = i && jl = j))
    in h(<fst(input@R(j,i)),<exp(g,b(j)),IdI(i)>>,Ininr(j,i))
    else h(<fst(input@R(j,i)),<exp(g,b(j)),IdI(i)>>,IgarbR(j,i)).

substeq Meq.
euf H0.
case H1.
depends R(jl,il), R1(jl,il).

by use ddhnotuple with  fst(input@R(jl,il)),<exp(g,b(jl)),IdI(il)>, fst(input@I1(il,jl)),a(il).

substeq Meq.
euf H0.
case H2.
depends R(j,i), R1(j,i).
Qed.

goal [Ror] helper_wa2 :
  forall (i,j:index),
    happens(I1(i,j)) =>
    cond@I1(i,j) =>

      Nr(j) = fst(snd(input@I1(i,j))) &&
      exp(g,b(j)) = fst(input@I1(i,j))
     .
Proof.
 intro i j.
 expand cond.

 case    try find jl,il such that
       (<Ni(i),fst(snd(input@I1(i,j)))> = <Ni(il),Nr(jl)> &&
        (il = i && jl = j))
     in h(<fst(input@I1(i,j)),<exp(g,a(i)),IdR(j)>>,Ininr(j,i))
     else h(<fst(input@I1(i,j)),<exp(g,a(i)),IdR(j)>>,IgarbI(j,i)).
substeq Meq1.
euf Meq.
by use ddhnotuple with fst(input@I1(il,jl)),<exp(g,a(il)),IdR(jl)>, fst(input@R(jl,il)),b(jl).
by depends I1(il,jl),I14(il,jl).

substeq Meq1.
euf Meq.
by use ddhnotuple with fst(input@I1(i,j)),<exp(g,a(i)),IdR(j)>, fst(input@I1(i,j)),a(i).
Qed.


equiv [Ror] final.
Proof.

globalprf seq(il,jl->  h( exp(exp(g,a(il)),b(jl)), Ininr(jl,il))  )  , news.

rename seq(i,j ->  n_PRF(i,j)), seq(i,j ->  idealkeys(i,j)), tk.

diffeq.
case (try find jl0,il0 such that
   (<fst(input@I2(il,jl)),<exp(g,a(il)),IdR(jl)>> = exp(exp(g,a(il0)),b(jl0)) &&
    (jl0 = jl && il0 = il))
 in idealkeys(jl0,il0)
 else h(<fst(input@I2(il,jl)),<exp(g,a(il)),IdR(jl)>>,Ininr(jl,il))).
by forceuse ddhnotuple with  fst(input@I2(il,jl)),<exp(g,a(il)),IdR(jl)>, exp(g,a(il)),b(jl).


forceuse helper_wa2 with i,j.
case (try find jl,il such that
   (<Ni(i),fst(snd(input@I1(i,j)))> = <Ni(il),Nr(jl)> && (il = i && jl = j))
 in
   try find jl,il such that
     (exp(fst(input@I1(i,j)),a(i)) = exp(exp(g,a(il)),b(jl)) &&
      (jl = j && il = i))
   in idealkeys(jl,il) else h(exp(fst(input@I1(i,j)),a(i)),Ininr(j,i))
 else h(exp(fst(input@I1(i,j)),a(i)),IgarbI(j,i))).
substeq Meq1.

case (try find jl0,il0 such that
   (exp(fst(input@I1(il,jl)),a(il)) = exp(exp(g,a(il0)),b(jl0)) &&
    (jl0 = jl && il0 = il))
 in idealkeys(jl0,il0) else h(exp(fst(input@I1(il,jl)),a(il)),Ininr(jl,il))).

use H2 with jl,il.

by forceuse ddhcommu with il,jl.

by use H2 with j,i.

by expand exec.

case (try find jl0,il0 such that
   (<fst(input@I1(il,jl)),<exp(g,a(il)),IdR(jl)>> = exp(exp(g,a(il0)),b(jl0)) &&
    (jl0 = jl && il0 = il))
 in idealkeys(jl0,il0)
 else h(<fst(input@I1(il,jl)),<exp(g,a(il)),IdR(jl)>>,Ininr(jl,il))) .
by forceuse ddhnotuple with fst(input@I1(il,jl)),<exp(g,a(il)),IdR(jl)>,exp(g,a(il)),b(jl).

case (try find jl0,il0 such that
   (<exp(g,a(il)),<fst(input@I1(il,jl)),IdI(il)>> = exp(exp(g,a(il0)),b(jl0)) &&
    (jl0 = jl && il0 = il))
 in idealkeys(jl0,il0)
 else h(<exp(g,a(il)),<fst(input@I1(il,jl)),IdI(il)>>,Ininr(jl,il))) .
by forceuse ddhnotuple with exp(g,a(il)),<fst(input@I1(il,jl)),IdI(il)>, exp(g,a(il)),b(jl).

case (try find jl0,il0 such that
   (<fst(input@R(jl,il)),<exp(g,b(jl)),IdI(il)>> = exp(exp(g,a(il0)),b(jl0)) &&
    (jl0 = jl && il0 = il))
 in idealkeys(jl0,il0)
 else h(<fst(input@R(jl,il)),<exp(g,b(jl)),IdI(il)>>,Ininr(jl,il))).
by forceuse ddhnotuple with fst(input@R(jl,il)),<exp(g,b(jl)),IdI(il)>, exp(g,a(il)),b(jl).

case try find jl,il such that
     (<fst(input@R(j,i)),<exp(g,b(j)),IdI(i)>> = exp(exp(g,a(il)),b(jl)) &&
      (jl = j && il = i))
   in idealkeys(jl,il)
   else h(<fst(input@R(j,i)),<exp(g,b(j)),IdI(i)>>,Ininr(j,i)).
by forceuse ddhnotuple with fst(input@R(jl,il)),<exp(g,b(jl)),IdI(il)>, exp(g,a(il)),b(jl).

substeq Meq.
by fa.

(* R1 case *)
forceuse helper_wa with i,j.
case (try find jl,il such that
   (<fst(snd(input@R(j,i))),Nr(j)> = <Ni(il),Nr(jl)> && (il = i && jl = j))
 in
   try find jl,il such that
     (exp(fst(input@R(j,i)),b(j)) = exp(exp(g,a(il)),b(jl)) &&
      (jl = j && il = i))
   in idealkeys(jl,il) else h(exp(fst(input@R(j,i)),b(j)),Ininr(j,i))
 else h(exp(fst(input@R(j,i)),b(j)),IgarbR(j,i))).
substeq Meq1.

case (try find jl0,il0 such that
   (exp(fst(input@R(jl,il)),b(jl)) = exp(exp(g,a(il0)),b(jl0)) &&
    (jl0 = jl && il0 = il))
 in idealkeys(jl0,il0) else h(exp(fst(input@R(jl,il)),b(jl)),Ininr(jl,il))).
by use H2 with jl,il.

by use H2 with j,i.
case (try find jl0,il0 such that
   (<exp(g,b(jl)),<fst(input@R(jl,il)),IdR(jl)>> = exp(exp(g,a(il0)),b(jl0)) &&
    (jl0 = jl && il0 = il))
 in idealkeys(jl0,il0)
 else h(<exp(g,b(jl)),<fst(input@R(jl,il)),IdR(jl)>>,Ininr(jl,il))).

by forceuse ddhnotuple with exp(g,b(jl)),<fst(input@R(jl,il)),IdR(jl)>,exp(g,a(il)),b(jl).
Qed.
