(*******************************************************************************

Internet Key Exchange (IKE) Version 1, with Pre-Shared Key.

Defined in RFC2409: https://datatracker.ietf.org/doc/html/rfc2409

Claimed to be Post-Quantum secure in https://datatracker.ietf.org/doc/html/rfc8784

# Protocol Description

We consider the phase 1 of the aggressive mode.

Each pairing of agents as a pre-shared key, psk, that will be used only once.


The key exchange is given as

            Initiator(i)                      Responder(j)
           -----------                      -----------
             g^ai, Nii, IDi -->
                                  <--    g^bj, Nrj, IDj, HASH_R
             HASH_I           -->


where
    SKEYID := prf(psk(i,j), Nii | Nrj),
    HASH_I = prf(SKEYID, g^ai | g^bj | Idi )
    HASH_R = prf(SKEYID, g^bj | g^ar | IDij )

The final derived key is
        SKEYID_d = prf(SKEYID, g^aibj)


Remark that we abstract away from some implementation details, and do not model the
cookies or the headers.


# Threat Model

We consider a set of pre-shared keys psk(i,j) between a set of i distinct Initiator and j Responder.
We consider the system `((!_j R: ResponderI(j)) | (!_i I: InitiatorI(i)))`
Where responder j is willing to talk to any of the initiators.

The attacker does not have any pre-shared key.

*******************************************************************************)

set postQuantumSound = true.

(* include Basic. *)

set oldCompletion = true.

hash h

(* pre-shared keys *)
name psk : index * index -> message.

(* DDH randomnesses *)
name a : index -> message
name b : index -> message

abstract g : message
abstract exp : message * message -> message

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

name Ininr  : index * index  -> message
name IgarbI : index * index -> message
name IgarbR : index * index -> message

process InitiatorI(i:index) =
  out(cI, <exp(g,a(i)), < Ni(i), IdI(i) >>);

  in(cI, m);
  (* find the preshared key in the database corresponding to the identity *)
  try find j such that fst(snd(snd(m)))(*RIdR*) = IdR(j) in
    if  snd(snd(snd(m)))(*HashR*) =  h(<  fst(m)(*gB*), < exp(g,a(i))  , IdR(j)> > ,
        (* idealized key computation *)
        try find il, jl such that <Ni(i),fst(snd(m))(*Nr*)> = <Ni(il),Nr(jl)> &&
         il = i && jl = j in
             Ininr(i,j)
        else
             IgarbI(i,j)
          ) then
       let finalkey = h( exp( fst(m)(*gB*) ,a(i)),
        (* idealized key computation *)
        try find il, jl such that <Ni(i),fst(snd(m))(*Nr*)> = <Ni(il),Nr(jl)> &&
         il = i && jl = j in
             Ininr(i,j)
        else
             IgarbI(i,j)
       ) in
       out(cI,  h(<exp(g,a(i)), < fst(m)(*gB*) , IdI(i)> > ,
        (* idealized key computation *)
        try find il, jl such that <Ni(i),fst(snd(m))(*Nr*)> = <Ni(il),Nr(jl)> &&
         il = i && jl = j in
             Ininr(i,j)
        else
             IgarbI(i,j)
)  )


process ResponderI(j:index) =
  in(cI, m);
  (* find the preshared key in the database corresponding to the identity *)
  try find i such that snd(snd(m))(*RIdi*) = IdI(i) in
    out(cR, <exp(g,b(j)), <Nr(j), < IdR(j)  ,  h(<exp(g,b(j)), <fst(m)(*gA*), IdR(j)> > ,
        (* idealized key computation *)
        try find il, jl such that < fst(snd(m)),Nr(j)> = <Ni(il),Nr(jl)> &&
         il = i && jl = j in
             Ininr(i,j)
        else
             IgarbR(i,j)
        )   >  >  > );

    in(cR, m2);
    if m2 =  h(<fst(m)(*gA*), <exp(g,b(j)), IdI(i)> > ,
        (* idealized key computation *)
        try find il, jl such that < fst(snd(m)),Nr(j)> = <Ni(il),Nr(jl)> &&
         il = i && jl = j in
             Ininr(i,j)
        else
             IgarbR(i,j)
        ) then
       out(cR, ok)

system [Ideal1] ((!_j R: ResponderI(j)) | (!_i I: InitiatorI(i))).



(* We prove that the main expression and the ideal 1 are equivalent. *)

(* We start with 3 global prf applications, renaming the prf name to the one we want after each application. *)
system Main1 = [Main/left] with gprf (il,jl:index),  h(<Ni(il), Nr(jl) > ,psk(il,jl)).
system Main2 = [Main1] with rename Forall (i,j:index), equiv(diff(n_PRF(i,j), Ininr(i,j))).


system Main3 = [Main2] with gprf (il,jl:index),  h(<Ni(il), fst(snd(input@I1(il,jl))) > ,psk(il,jl)).
system Main4 = [Main3] with rename Forall (i,j:index), equiv(diff(n_PRF1(i,j), IgarbI(i,j))).

system Main5 = [Main4] with gprf (il,jl:index),  h(<fst(snd(input@R(jl,il))),Nr(jl) > ,psk(il,jl)).
system Main6 = [Main5] with rename Forall (i,j:index), equiv(diff(n_PRF2(i,j), IgarbR(i,j))).


axiom  [Main6,Ideal1/right] tryfind : forall (i,j:index), pred(I1(i,j)) = pred(I2(i,j)).

equiv [Main6,Ideal1/right] test.
Proof.

  diffeq => *. 
   (* From here, we need to prove that we indede get ideal keys everywhere. Mostly dumb manipulations of all the conditions introduced by the prf tactic, that are all contractory.
     *)
    + intro *. 
      case  try find il0,jl0 such that _ in IgarbI(il0,jl0) else _.
        ++ intro [?? [_ ->]].
           fa; auto. 
        ++ rewrite tryfind. 
           intro [Abs TFeq].
           use Abs with i,j; auto.

    + intro *.
      case try find il0,jl0 such that _ in IgarbI(il0,jl0) else _.
        ++ intro [?? [_ ->]]. 
           fa; auto.
        ++ intro [Abs TFeq].
           use Abs with i,j; auto.

    + intro *.
      case  try find il0,jl0 such that _ in IgarbI(il0,jl0) else _.
        ++ intro [?? [_ ->]]. 
           fa; auto.
        ++ intro [Abs TFeq].
           use Abs with i,j; auto.

    + intro *.
      case try find il,jl such that _ in Ininr(i,j) else IgarbR(i,j).
        ++ intro [?? [[_ _ _] ->]]. 
           case try find il0,jl0 such that _  in Ininr(il0,jl0) else _.
             +++ auto. 
             +++ intro [Abs TFeq2].
                 use Abs with i,j; auto.
        ++ intro [Abs TFeq].
           case try find il0,jl0 such that _ in Ininr(il0,jl0) else _.
             +++ intro [?? [_ TFeq2]]. 
                 by use Abs with i,j.
             +++ intro [Abs2 TFeq2].
                 case try find il0,jl0 such that _ in IgarbI(il0,jl0) else _.
                   - intro [?? [_ _]]. 
                     by use Abs with i,j.
                   - intro [Abs3 TFeq3].
                     case try find il,jl such that _ in IgarbR(il,jl) else _.
                       -- intro [?? [_ ->]]. 
                          auto.
                       -- intro [[Abs4] TFeq4].
                          by use Abs4 with i,j.

    + intro *.
      case try find il,jl such that _ in Ininr(i,j) else IgarbR(i,j).
        ++ intro [?? [[_ _ _] ->]]. 
           case try find il0,jl0 such that _ in Ininr(il0,jl0) else _.
             +++ auto. 
             +++ intro [Abs _]. 
                 by use Abs with i,j.
        ++ case try find il0,jl0 such that _ in Ininr(il0,jl0) else _.
             +++ intro [?? [_ ->]]. 
                 intro [Abs _].
                 by use Abs with i,j.
             +++ intro [Abs _].
                 intro [Abs2 _].
                 case try find il0,jl0 such that _ in IgarbI(il0,jl0) else _.
                   - intro [?? [_ ->]]. 
                     use Abs with i,j; auto.
                   - case try find il,jl such that _ in IgarbR(il,jl) else _.
                       -- intro [?? [_ ->]]. 
                          auto.
                       -- intro [Abs3 _].
                          use Abs3 with i,j; auto.

    + intro *.
      case try find il,jl such that _ in IgarbR(il,jl) else _.
        ++ intro [?? [[_ _ _] ->]]. 
           case try find il,jl such that _ in Ininr(i,j) else IgarbR(i,j).
             +++ intro [?? [[_ _ _] ->]]. 
                 case try find il0,jl0 such that _ in Ininr(il0,jl0) else _.
                   - auto. 
                   - intro [Abs _].
                     use Abs with i,j; auto.

             +++ intro [Abs _].
                 case try find il0,jl0 such that _ in Ininr(il0,jl0) else _.
                   - intro [?? [_ ->]]. 
                     use Abs with i,j; auto.
                   - intro [Abs2 _].
                     case try find il0,jl0 such that _ in IgarbI(il0,jl0) else _.
                       -- intro [?? [_ ->]]. 
                          use Abs2 with i,j; auto.
                       -- intro [Abs3 _]; auto.
        ++ intro [Abs _].
           use Abs with i,j; auto.
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
        try find jl, il such that <Ni(i),fst(snd(m))(*Nr*)> = <Ni(il),Nr(jl)> &&
         il = i && jl = j in
         h(<  fst(m)(*gB*), < exp(g,a(i))  , IdR(j)> > ,    Ininr(j,i))
        else
           h(<  fst(m)(*gB*), < exp(g,a(i))  , IdR(j)> > ,  IgarbI(j,i))
           then
       out(cI,
        (* idealized key computation *)
        try find jl, il such that <Ni(i),fst(snd(m))(*Nr*)> = <Ni(il),Nr(jl)> &&
         il = i && jl = j in
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
        try find jl, il such that < fst(snd(m)),Nr(j)> = <Ni(il),Nr(jl)> &&
         il = i && jl = j in
            h(<exp(g,b(j)), <fst(m)(*gA*), IdR(j)> > ,   Ininr(j,i))
        else
          h(<exp(g,b(j)), <fst(m)(*gA*), IdR(j)> > ,     IgarbR(j,i))
           >  >  > );

    in(cR, m2);
    if m2 =
        (* idealized key computation *)
        try find jl, il such that < fst(snd(m)),Nr(j)> = <Ni(il),Nr(jl)> &&
         il = i && jl = j in
            h(<fst(m)(*gA*), <exp(g,b(j)), IdI(i)> > ,  Ininr(j,i))
        else
            h(<fst(m)(*gA*), <exp(g,b(j)), IdI(i)> > ,  IgarbR(j,i))
         then
       out(cR, ok)

system [Ideal2] ((!_j R: ResponderI2(j)) | (!_i I: InitiatorI2(i))).

(* We now prove the authentication on this ideal system. *)

goal [Ideal2] wa_1 (i,j:index[param]):
    happens(I1(i,j)) =>
    cond@I1(i,j) =>
    (exists (i0:index), happens(R(j,i0)) && R(j,i0) < I1(i,j) &&

      fst(output@R(j,i0)) = fst(input@I1(i,j)) &&
      fst(snd(output@R(j,i0))) = fst(snd(input@I1(i,j))) &&
      fst(snd(snd(output@R(j,i0)))) = fst(snd(snd(input@I1(i,j)))) &&
     fst(input@R(j,i0)) = fst(output@I(i))
     ).
Proof.
 intro Hap Cond.
 expand cond.

  case  try find jl,il such that
         (<Ni(i),fst(snd(input@I1(i,j)))> = <Ni(il),Nr(jl)> &&
          (il = i && jl = j))
       in h(<fst(input@I1(i,j)),<exp(g,a(i)),IdR(j)>>,Ininr(j,i))
       else h(<fst(input@I1(i,j)),<exp(g,a(i)),IdR(j)>>,IgarbI(j,i)).
    + (* Case 1 -> honnest skeyid *)
      intro [?? [[A [_ _]] B]].
      rewrite B in Cond.
      destruct Cond as [EUF _].
      euf EUF; try auto.
        ++ intro [Ord _ Eq].
           exists i.
           assert happens(R(j,i)) => //.
           assert happens(I(i)) => //.
           depends I(i), I1(i,j) => //.
        ++ intro [Ord _ Eq].
           use mutex_Ideal2_I1_I2 with i,j,j as H; by case H.

    +  (* Case 2 -> dishonnest skeyid, trivial as no one else computes this key *)
       intro [Abs Meq].
       rewrite Meq in Cond.
       destruct Cond as [EUF _].
       euf EUF; try auto.
       intro [Ord E] //. 
       use mutex_Ideal2_I1_I2 with i,j,j as H; by case H.
Qed.

goal [Ideal2] wa_2 (i,j:index[param]):
    happens(R1(j,i)) =>
    exec@R1(j,i) =>
     happens(I(i)) &&
  fst(input@R(j,i)) = fst(output@I(i)) &&
    fst(snd(input@R(j,i))) = fst(snd(output@I(i))) &&
   snd(snd(input@R(j,i))) = snd(snd(output@I(i))).

Proof.
  intro Hap Ex.
  expand exec.
  expand cond.
  destruct Ex as [_ EUF].
  depends R(j,i), R1(j,i) => //.
  intro OrdR.
  case try find jl,il such that
        <fst(snd(input@R(j,i))),Nr(j)> = <Ni(il),Nr(jl)> && il = i && jl = j
       in   h(<fst(input@R(j,i)),<exp(g,b(j)),IdI(i)>>,Ininr(j,i))
       else h(<fst(input@R(j,i)),<exp(g,b(j)),IdI(i)>>,IgarbR(j,i)).
    + intro [jl il [[Cond _ _] Meq]].
      rewrite Meq in EUF.
      euf EUF; try auto.
      ++ intro [H _].
         case H.
         * by depends R(j,i), R2(j,i).
         * use mutex_Ideal2_R1_R2 with j,i as H2; by case H2.
      ++ intro [OrdI Meq2 _].
         depends I(i), I1(i,j).
         case OrdI; auto. 
         intro OrdI2.
         executable pred(R1(j,i)) => //.
         intro Exec.
         use Exec with R(j,i) => //.
    + intro Abs.
      destruct Abs as [Abs Meq2].
      rewrite Meq2 in EUF.
      euf EUF; try auto.
      intro [H _]; case H.
       * by depends R(j,i), R2(j,i).
       * use mutex_Ideal2_R1_R2 with j,i as H2; by case H2.
Qed.


(*********************************)
(* Final game for Real or Random *)

(* this is ideal 2, where in addition each party IdI(i) in the end either outputs the derived key, or an idealied key ideal(i,j) if it thinks it is talking to party IdR(j). *)

name idealkeys : index * index -> message.

process InitiatorRoR(i:index) =
  out(cI, <exp(g,a(i)), < Ni(i), IdI(i) >>);

  in(cI, m);
  (* find the preshared key in the database corresponding to the identity *)
  try find j such that fst(snd(snd(m)))(*RIdR*) = IdR(j) in
    if  snd(snd(snd(m)))(*HashR*) =
        (* idealized key computation *)
        try find il, jl such that   (<Ni(i),fst(snd(m))(*Nr*)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
         h(<  fst(m)(*gB*), < exp(g,a(i))  , IdR(j)> > ,    Ininr(j,i))
        else
           h(<  fst(m)(*gB*), < exp(g,a(i))  , IdR(j)> > ,  IgarbI(j,i))
           then
       out(cI,
        (* idealized key computation *)
        try find il, jl such that   (<Ni(i),fst(snd(m))(*Nr*)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
             h(<exp(g,a(i)), < fst(m)(*gB*) , IdI(i)> > ,Ininr(j,i))
        else
            h(<exp(g,a(i)), < fst(m)(*gB*) , IdI(i)> > , IgarbI(j,i)));

       out(cI,diff(      try find il, jl such that   (<Ni(i),fst(snd(m))(*Nr*)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
             h( exp(fst(m),a(i)), Ininr(j,i))
        else
             h( exp(fst(m),a(i)),  IgarbI(j,i)), idealkeys(i,j))).


process ResponderRoR(j:index) =
  in(cI, m);
  (* find the preshared key in the database corresponding to the identity *)
  try find i such that snd(snd(m))(*RIdi*) = IdI(i) in
    out(cR, <exp(g,b(j)), <Nr(j), < IdR(j)  ,
        (* idealized key computation *)
        try find il, jl such that   (< fst(snd(m)),Nr(j)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
            h(<exp(g,b(j)), <fst(m)(*gA*), IdR(j)> > ,   Ininr(j,i))
        else
          h(<exp(g,b(j)), <fst(m)(*gA*), IdR(j)> > ,     IgarbR(j,i))
           >  >  > );

    in(cR, m2);
    if m2 =
        (* idealized key computation *)
        try find il, jl such that   (< fst(snd(m)),Nr(j)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
            h(<fst(m)(*gA*), <exp(g,b(j)), IdI(i)> > ,  Ininr(j,i))
        else
            h(<fst(m)(*gA*), <exp(g,b(j)), IdI(i)> > ,  IgarbR(j,i))
         then
       out(cR,diff(
        try find il, jl such that   (< fst(snd(m)),Nr(j)> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j)) in
              h( exp(fst(m),b(j)), Ininr(j,i))
        else
               h( exp(fst(m),b(j)),  IgarbR(j,i))
, idealkeys(i,j))).

system [Ror] ((!_j R: ResponderRoR(j)) | (!_i I: InitiatorRoR(i))).



axiom [Ror] ddhcommu : forall (i,j:index), exp(exp(g,a(i)),b(j)) =  exp(exp(g,b(j)),a(i)) .
axiom [Ror] ddhnotuple : forall (m1,m2,m3,m4:message), exp(m3,m4) <> <m1,m2>.

(* we first prove two small authentication lemmas, so that if we reach the ideal key computation, we now we have the correct parameters. *)

goal [Ror] helper_wa (i,j:index[param]):
    happens(R1(j,i)) =>
    exec@R1(j,i) =>
    fst(snd(input@R(j,i))) = Ni(i) &&
    fst(input@R(j,i)) = exp(g,a(i))
.

Proof.
  intro Hap Exec.
  expand exec.
  destruct Exec as [Pred Cond].
  expand cond.
  case try find il,jl such that
       (<fst(snd(input@R(j,i))),Nr(j)> = <Ni(il),Nr(jl)> && (il = i && jl = j))
     in h(<fst(input@R(j,i)),<exp(g,b(j)),IdI(i)>>,Ininr(j,i))
     else h(<fst(input@R(j,i)),<exp(g,b(j)),IdI(i)>>,IgarbR(j,i)).
    + intro [?? [[Eq1 [_ _]] Eq2]].
      rewrite Eq2 in Cond.  
      euf Cond => //.
      * by depends R(j,i), R1(j,i). 
      * by depends R(j,i), R1(j,i). 
      * intro [H _]; case H.
        by depends R(j,i), R2(j,i). 
        use mutex_Ror_R2_R1 with j,i as HH; by case HH.             
      * intro [Ord1 Ord2 _]. 
      by use ddhnotuple with  fst(input@R(j,i)),<exp(g,b(j)),IdI(i)>, fst(input@I1(i,j)),a(i).
    + intro [Abs Meq].
      rewrite Meq in Cond.
      euf Cond; try auto.
      * by depends R(j,i), R1(j,i).
      * by depends R(j,i), R1(j,i).
      * intro [H _]; case H.
        by depends R(j,i), R2(j,i). 
        use mutex_Ror_R2_R1 with j,i as HH; by case HH.             
Qed.




goal [Ror] helper_wa2 (i,j:index[param]):
    happens(I1(i,j)) =>
    exec@I1(i,j) =>

      Nr(j) = fst(snd(input@I1(i,j))) &&
      exp(g,b(j)) = fst(input@I1(i,j))
     .
Proof.
  intro Hap Exec.
  expand exec.
  expand cond.
  destruct Exec as [_ [CondTF _]].
  case    try find il,jl such that
        (<Ni(i),fst(snd(input@I1(i,j)))> = <Ni(il),Nr(jl)> &&
         (il = i && jl = j))
      in h(<fst(input@I1(i,j)),<exp(g,a(i)),IdR(j)>>,Ininr(j,i))
      else h(<fst(input@I1(i,j)),<exp(g,a(i)),IdR(j)>>,IgarbI(j,i)).
    + intro [?? [[Eq [_ _]] Meq]].
      rewrite Meq in CondTF.
      euf CondTF => //.
        ++ by use ddhnotuple with fst(input@I1(i,j)),<exp(g,a(i)),IdR(j)>, fst(input@R(j,i)),b(j).
        ++ intro OrdI.
           by depends I1(i,j),I4(i,j).
        ++ use mutex_Ror_I2_I1 with i,j,j as HH; by case HH.
    + intro [Abs Meq].
      rewrite Meq in CondTF.
      euf CondTF; try auto.
      ++ by use ddhnotuple with fst(input@I1(i,j)),<exp(g,a(i)),IdR(j)>, fst(input@I1(i,j)),a(i).
      ++ use mutex_Ror_I2_I1 with i,j,j as HH; by case HH.
Qed.

system Ror2 = [Ror/left] with gprf (il,jl:index),   h( exp(exp(g,a(il)),b(jl)), Ininr(jl,il))   .
system Ror3 =  [Ror2] with rename Forall (i,j:index), equiv(diff(n_PRF3(i,j), idealkeys(i,j))).

axiom  [Ror3, Ror/right] ddhcommu2 : forall (i,j:index), exp(exp(g,a(i)),b(j)) =  exp(exp(g,b(j)),a(i)) .
axiom  [Ror3, Ror/right] ddhnotuple1 : forall (m1,m2,m3,m4:message), exp(m3,m4) <> <m1,m2>.


(* By transitivity, we inherit the lemma on Ror to Ror2 *)
global goal [Ror/left,Ror2] helper_wa_equiv (i, j:index[param]):
  [happens(R1(j,i))] ->
  equiv(
    exec@R1(j,i) =>
    input@R1(j,i) = input@R1(j,i) &&
    (fst(snd(input@R(j,i))) = Ni(i) &&
    fst(input@R(j,i)) = exp(g,a(i)))
  ).
Proof.
  intro H2.
  use prf_from_Ror_to_Ror2 with <a(i),Ni(i)>.
    + use H with R(j,i) => //.
      use H with R1(j,i) => //.
      fa 0.
      enrich frame@R(j,i).
      enrich frame@R1(j,i).
      repeat fa 1.
      repeat fa 2.
      repeat fa 3.
      apply H1.
      depends R(j,i), R1(j,i) => //.
    + intro i0 j0.
      by fresh 1.
Qed.

goal [Ror2] helper_wa_aux3 (i,j:index[param]):
    happens(R1(j,i)) =>
    exec@R1(j,i) =>
    input@R1(j,i) = input@R1(j,i) &&
    (fst(snd(input@R(j,i))) = Ni(i) &&
    fst(input@R(j,i)) = exp(g,a(i))).
Proof.
  intro Hap.
  rewrite equiv -helper_wa_equiv i j.
  auto.
  intro Ex.
  use helper_wa with i,j; auto.
Qed.



global goal [Ror2,Ror3] helper_wa_equiv1 (i, j:index[param]):
  [happens(R1(j,i))] ->
   equiv(
  exec@R1(j,i) =>
input@R1(j,i) = input@R1(j,i) &&
    (fst(snd(input@R(j,i))) = Ni(i) &&
    fst(input@R(j,i)) = exp(g,a(i)))
).
Proof.
  intro H2.
  use rename_from_Ror2_to_Ror3 with <a(i),Ni(i)>.
    + use H with R(j,i) => //.
      use H with R1(j,i) => //.
      fa 0.
      enrich frame@R(j,i).
      enrich frame@R1(j,i).
      repeat fa 1.
      repeat fa 2.
      apply H1.
      depends R(j,i), R1(j,i); auto.
    + intro i0 j0.
      by fresh 1.
Qed.


goal [Ror3] helper_wa_aux4 (i,j:index[param]):
    happens(R1(j,i)) =>
    exec@R1(j,i) =>
     input@R1(j,i) = input@R1(j,i) &&
    (fst(snd(input@R(j,i))) = Ni(i) &&
    fst(input@R(j,i)) = exp(g,a(i)))
.
Proof.
  intro Hap.
  rewrite equiv -helper_wa_equiv1  i j.
  auto.
  intro Exec.
  use helper_wa_aux3 with i,j; auto.
Qed.


goal [Ror3, Ror/right] helper_wa3 (i,j:index[param]):
    happens(R1(j,i)) =>
    exec@R1(j,i) =>
    fst(snd(input@R(j,i))) = Ni(i) &&
    fst(input@R(j,i)) = exp(g,a(i))
.
Proof.
  project.
  intro Hap Ex.
  use helper_wa_aux4 with i,j; auto.
  intro Hap Ex.
  use helper_wa with i,j; auto.
Qed.


(* We now export helper wa 2 all the way to Ror3 *)
global goal [Ror/left,Ror2] helper_wa_equiv_2 :
  Forall (i,j:index[param]),
  [happens(I1(i,j))] ->
  equiv(
    exec@I1(i,j) =>
      Nr(j) = fst(snd(input@I1(i,j))) &&
      exp(g,b(j)) = fst(input@I1(i,j))
  ).
Proof.
  intro i j Hap.
  use prf_from_Ror_to_Ror2 with <b(j),Nr(j)>.
    + use H with I1(i,j) => //.
      fa 0.
      repeat fa 1.
      repeat fa 2.
      repeat fa 3.
      enrich frame@I1(i,j).
      apply H0.
    + intro i0 j0.
      by fresh 1.
Qed.


goal [Ror2] helper_wa_aux2 (i,j:index[param]):
    happens(I1(i,j)) =>
    exec@I1(i,j) =>
      Nr(j) = fst(snd(input@I1(i,j))) &&
      exp(g,b(j)) = fst(input@I1(i,j)).
Proof.
  intro Hap.
  rewrite equiv -helper_wa_equiv_2  i j.
  auto.
  intro Ex.
  by use helper_wa2 with i, j.
Qed.

global goal [Ror2,Ror3] helper_wa_equiv_3 :
  Forall (i,j:index[param]),
    [happens(I1(i,j))] ->
    equiv(
      exec@I1(i,j) =>
        Nr(j) = fst(snd(input@I1(i,j))) &&
        exp(g,b(j)) = fst(input@I1(i,j))
    ).
Proof.
  intro i j Hap.
  use rename_from_Ror2_to_Ror3 with <b(j),Nr(j)>.
    + use H with I1(i,j) => //.
      fa 0.
      repeat fa 1.
      repeat fa 2.
      repeat fa 3.
      enrich frame@I1(i,j).
      apply H0.
    + intro i0 j0.
      by fresh 1.
Qed.

goal [Ror3] helper_wa_aux5 (i,j:index[param]):
    happens(I1(i,j)) =>
    exec@I1(i,j) =>

      Nr(j) = fst(snd(input@I1(i,j))) &&
      exp(g,b(j)) = fst(input@I1(i,j))
     .
Proof.
  intro Hap.
  rewrite equiv -helper_wa_equiv_3  i j.
  auto.
  intro Ex.
  by use helper_wa_aux2 with i, j.
Qed.


goal [Ror3, Ror/right] helper_wa4 (i,j:index[param]):
    happens(I1(i,j)) =>
    exec@I1(i,j) =>
      Nr(j) = fst(snd(input@I1(i,j))) &&
      exp(g,b(j)) = fst(input@I1(i,j)).
Proof.
  project.
  intro Hap Ex.
  by use helper_wa_aux5 with i,j.
  intro Hap Ex.
  by use helper_wa2 with i,j.
Qed.

equiv [Ror3,Ror/right] final.
Proof.
  diffeq => *.
    + intro *.
      case try find il,jl such that _ in idealkeys(il,jl) else _.
        - by use ddhnotuple1 with  fst(input@I2(i,j)),<exp(g,a(i)),IdR(j)>, exp(g,a(i)),b(j).
        -  intro *.
           fa; try auto.

    + intro *.
      use helper_wa4 with i,j; try auto.
      case try find il,jl such that _ in idealkeys(il,jl) else _.
        - intro [?? [[Exp [_ _]] ->]].
          case try find il0,jl0 such that _ in idealkeys(i,j) else _.
          auto.
          intro [Abs _].
          by use Abs with i,j.
       - case try find il0,jl0 such that _ in  h(exp(fst(att(frame@pred(I1(i,j)))),a(i)),Ininr(j,i))
                  else _.
         intro Ex [Abs _].
         use Abs with i,j => //.
         by rewrite ddhcommu2.
         intro [Abs _] [Abs2 _].
         by use Abs with i,j.

    + intro *.
      expand exec.
      case try find il,jl such that _
         in idealkeys(il,jl)
         else _.
      intro [?? [[_ [_ _]] ->]].
      by use ddhnotuple1 with  fst(input@I1(i,j)),<exp(g,a(i)),IdR(j)>, exp(g,a(i)),b(j).
      intro _.
      by fa.

    + intro *.
      case try find il,jl such that _
         in idealkeys(il,jl)
         else _.
      by use ddhnotuple1 with  exp(g,a(i)),<fst(input@I1(i,j)),IdI(i)>, exp(g,a(i)),b(j).
      intro _.
      by fa.

    + intro *.
      case try find il,jl such that
       _
         in idealkeys(il,jl)
         else _.
      by use ddhnotuple1 with  fst(input@R(j,i)),<exp(g,b(j)),IdI(i)>, exp(g,a(i)),b(j).
      intro _.
      by fa.

    + intro *.
      case try find il,jl such that _
         in idealkeys(il,jl)
         else _.
      by use ddhnotuple1 with  fst(input@R(j,i)),<exp(g,b(j)),IdI(i)>, exp(g,a(i)),b(j).
      intro _.
      by fa.

    + intro *.
      use helper_wa3 with i,j; try auto.
      case try find il0,jl0 such that
         _
       in
         _
       else  h(exp(fst(att(frame@pred(R(j,i)))),b(j)),IgarbR(j,i)).
        - intro [?? [[_ _ _] ->]].
          case (try find il,jl such that _
           in idealkeys(il,jl) else _).
          ** auto. 
          ** intro [Abs _].
             by use Abs with i,j.
        - intro [Abs _].
          by use Abs with i,j.

    + intro *.
      case try find il,jl such that _
         in idealkeys(il,jl)
         else _.
      by use ddhnotuple1 with exp(g,b(j)),<fst(input@R(j,i)),IdR(j)>,exp(g,a(i)),b(j).
      intro *.
      by fa.
Qed.
