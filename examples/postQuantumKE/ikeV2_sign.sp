(*******************************************************************************

Internet Key Exchange (IKE) Version 2, with Signatures

Defined in RFC7296: https://datatracker.ietf.org/doc/html/rfc7296

Extended with an additional pre-shared key for PQ soundness as described in
https://datatracker.ietf.org/doc/html/rfc8784


# Protocol Description

We consider the phase 1 with digital signatures.


            Initiator                        Responder
           -----------                      -----------
              g^xi, Ni        -->
                              <--            g^xr, Nr
            enc(Idi,Authi,k}  -->
                              <--           enc(IdR,Authr,k}



Where the keying material is derived as:
    SKEYSEED = prf(Ni | Nr, g^xixr)
    SK_p =  prf(SKEYSEED, Ni | Nr)
    SK_d =  prf2(SKEYSEED, Ni | Nr)

And:
    Authi = sign( g^xi, Ni, Nr, prf(SK_p,public_seed) ,pks(skI), skI)
    Authr = sign( g^xr, Nr, Ni, prf(SK_p, public_seed) ,pks(skR), skR)


In the PQ version, a pre-shared key PPK is included in the computation.
    SK_d =  prf(PPK, SK_p)

# Modeling

We model ` ((!_k !_l R: Responder(k,l)) | (!_i !_j I: Initiator(i,j))).`
Where Responder(k,l) is using skR(k) and is willing to talk to pkI(l), and
Initiator(i,j) is using skI(i) and is willing to talk to skR(j).

The pre-shared key between agent skI(i) and skR(j) should be used only once,
so we don't model multiple interactions between them.

In the following model, we remove multiple layers of integrity and encryption, keeping the minimal required for the authentication and real or random.

*******************************************************************************)
set timeout=10.
set postQuantumSound = true.

hash h

(* pre-shared keys *)
name psk : index -> index -> message

(* long term keys *)
name skI :index ->  message
name skR : index -> message


(* DDH randomnesses *)
name xi :  index -> index ->  message
name xr :  index -> index -> message

abstract g : message
abstract exp : message -> message -> message

(* fresh randomness *)
name Ni : index -> index ->   message
name Nr : index -> index ->   message

abstract ok:message
abstract ko:message

channel cI
channel cR
signature sign,checksign,pk

(* first hash function is a hseed, with public key -> we only need collision resistance *)
hash hseed
name seedpubkey : message

hash prfp
hash prfd


(* Main model *)

process Initiator(i,j:index) =
  out(cI, <exp(g,xi(i,j)), Ni(i,j)>);

  in(cI, m);



  SI : out(cI,sign(  < exp(g,xi(i,j))
               , <Ni(i,j),
                  <snd(m)(*Nr*),
                   prfp(  hseed( <<Ni(i,j),snd(m)(*Nr*)>,  exp(fst(m),xi(i,j))>, seedpubkey )(* SKEYSEED *),
                        <Ni(i,j),snd(m)(*Nr*)> )
                   >>>,  skI(i)  )
     );
  in(cI,signed);
  if checksign( signed, pk(skR(j))) =
      < fst(m)(*gI*)
               , <snd(m)(*Nr*),
                  <Ni(i,j)(*Ni*),
                   prfp(  hseed( < <Ni(i,j),snd(m)(*Nr*)>,   exp(fst(m),xi(i,j))>, seedpubkey ) (* SKEYSEED *),
                  <Ni(i,j),snd(m)(*Nr*)> )
                   >>> then
     FI :  out(cR, ok).


process Responder(i,j:index) =
  in(cR,m);
  out(cR, <exp(g,xr(i,j)), Nr(i,j)>);

  in(cR, signed);
  if checksign( signed, pk(skI(j))) =
      < fst(m)(*gI*)
               , <snd(m)(*Ni*),
                  <Nr(i,j)(*Nr*),
                   prfp(  hseed(< <snd(m)(*Ni*),Nr(i,j)>,  exp(fst(m),xr(i,j))>, seedpubkey)(* SKEYSEED *),
                   <snd(m)(*Ni*),Nr(i,j)> )
                   >>> then
    SR:  out(cR,
      sign(  < exp(g,xr(i,j))
               , <Nr(i,j),
                  <snd(m)(*Ni*),
                   prfp(  hseed(<  <snd(m)(*Ni*),Nr(i,j)>,  exp(fst(m),xi(i,j))>,seedpubkey)(* SKEYSEED *),
                      <snd(m)(*Ni*),Nr(i,j)> )
                   >>>,  skR(i)
)).





system  out(cI, seedpubkey); ((!_k !_l R: Responder(k,l)) | (!_i !_j I: Initiator(i,j))).

(*****************)
(* Security game *)


(* We simply reveal the keys in the end, they should be indistinguishable from perfect keys *)

name idealkeys : index -> index -> index -> index -> message

process InitiatorRoR(i,j:index) =
   out(cI, <exp(g,xi(i,j)), Ni(i,j)>);

  in(cI, m);



  SI : out(cI,sign(  < exp(g,xi(i,j))
               , <Ni(i,j),
                  <snd(m)(*Nr*),
                   prfp(  hseed( <<Ni(i,j),snd(m)(*Nr*)>,  exp(fst(m),xi(i,j))>, seedpubkey )(* SKEYSEED *),
                        <Ni(i,j),snd(m)(*Nr*)> )
                   >>>,  skI(i)  )
     );
  in(cI,signed);
  if checksign( signed, pk(skR(j))) =
      < fst(m)(*gI*)
               , <snd(m)(*Nr*),
                  <Ni(i,j)(*Ni*),
                   prfp(  hseed( < <Ni(i,j),snd(m)(*Nr*)>,   exp(fst(m),xi(i,j))>, seedpubkey ) (* SKEYSEED *),
                  <Ni(i,j),snd(m)(*Nr*)> )
                   >>> then


    FI :   out(cR,
    diff( prfd(hseed( < <Ni(i,j),snd(m)(*Nr*)>,   exp(fst(m),xi(i,j))>,seedpubkey)(* SKEYSEED *),psk(i,j)),
       try find jf,kf such that  snd(m) = Nr(jf,kf) in
	 idealkeys(kf,jf,j,i)
       else fail)
       ).


process ResponderRor(i,j:index) =
  in(cR,m);
  out(cR, <exp(g,xr(i,j)), Nr(i,j)>);

  in(cR, signed);
  if checksign( signed, pk(skI(j))) =
      < fst(m)(*gI*)
               , <snd(m)(*Ni*),
                  <Nr(i,j)(*Nr*),
                   prfp(  hseed(< <snd(m)(*Ni*),Nr(i,j)>,  exp(fst(m),xr(i,j))>, seedpubkey)(* SKEYSEED *),
                   <snd(m)(*Ni*),Nr(i,j)> )
                   >>> then
    SR:  out(cR,
      sign(  < exp(g,xr(i,j))
               , <Nr(i,j),
                  <snd(m)(*Ni*),
                   prfp(  hseed(<  <snd(m)(*Ni*),Nr(i,j)>,  exp(fst(m),xi(i,j))>,seedpubkey)(* SKEYSEED *),
                      <snd(m)(*Ni*),Nr(i,j)> )
                   >>>,  skR(i)
));


 FR : out(cR, diff( prfd(  hseed(<  <snd(m)(*Ni*),Nr(i,j)>,  exp(fst(m),xr(i,j))>,seedpubkey)(* SKEYSEED *), psk(j,i))
              ,        try find jf,kf such that  snd(m) = Ni(jf,kf) in
                    idealkeys(j,kf,i,jf)
                        else fail
)).



system [core]  out(cI, seedpubkey); ((!_k !_l R: ResponderRor(k,l)) | (!_i !_j I: InitiatorRoR(i,j))).

system core2 = [core/left] with gprf (il,jl,kl,ll:index),
 prfd(  hseed( < <Ni(il,jl),Nr(kl,ll)>,  exp(exp(g,xr(kl,ll)),xi(il,jl))>, seedpubkey  )(* SKEYSEED *), psk(ll,kl)).

system core3 =  [core2/left] with rename forall (l,k,i,j:index), equiv(diff( n_PRF(l,k,j,i),  idealkeys(l,k,j,i))).



goal [core3/left,core/right] authR : forall (i,j:index),
       happens(FR(i,j)) => exec@FR(i,j) =>
           exists (l:index), SI(j,l) < FR(i,j) &&
                      fst(input@R(i,j)) = exp(g,xi(j,l)) &&
                      snd(input@R(i,j)) = Ni(j,l).
Proof.
intro i j.
expand exec.
executable  pred(FR(i,j)).
depends  SR(i,j),FR(i,j).
use H1 with SR(i,j).
expand exec. expand cond.
euf H3.
exists j0.
case H0. depends R(i,j),FR(i,j).
Qed.

goal [core3/left,core/right] authI : forall (i,j:index),
       happens(FI(i,j)) => exec@FI(i,j) =>
                      SR(j,i) < FI(i,j) &&
                      fst(input@SI(i,j)) = exp(g,xr(j,i)) &&
                      snd(input@SI(i,j)) = Nr(j,i).
Proof.
intro i j.
expand exec. expand cond.
euf H0.

depends SI(i,j), FI(i,j).

assert SR(j,l) < FI(i,j).
case H1.
executable pred(FI(i,j)).
use H2 with SR(j,l).
expand exec.
expand cond.
by euf H4.
Qed.


axiom [core3/left,core/right] ddhcommu : forall (i,j,k,l:index), exp(exp(g,xi(i,j)),xr(k,l)) =  exp(exp(g,xr(k,l)),xi(i,j)) .

equiv [core3/left,core/right] final.
Proof.

diffeq.



(* I part *)
use authI with i,j.

case try find il,jl,kl,ll such that _ in idealkeys(il,jl,kl,ll) else _.
rewrite Meq1.
collision.

case try find jf,kf such that _
in _ else fail.
rewrite Meq5.

by use H2 with jl,il.

by use H2 with i,j,j,i.


(* R part *)
use authR with k,l.
case try find il,jl,kl,ll such that _
 in  idealkeys(il,jl,kl,ll)
 else _.

rewrite Meq1.
collision.

case try find jf,kf such that _ in _ else fail.
rewrite Meq5.

by use H2 with l,jl.

rewrite Meq in H2.
rewrite Meq0 in H2.

use H2 with l,l0,k ,l.


use ddhcommu with l,l0,k,l.
Qed.
