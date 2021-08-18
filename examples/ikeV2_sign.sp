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
                                  <--        g^xr, Nr
            HDR, enc(Idi,Authi,k} -->
                                  <--       HDR, enc(IdR,Authr,k}



Authi = sign( g^xi, Ni, Nr, prf(SK_pi, IDr') ,pks(skI), skI)
Authr = sign( g^xr, Nr, Ni, prf(SK_pr, IDr') ,pks(skR), skR)

Where the keying material is derived as:
SKEYSEED = prf(Ni | Nr, g^ir)

   {SK_d | SK_ai | SK_ar | SK_ei | SK_er | SK_pi | SK_pr}
                   = prf+ (SKEYSEED, Ni | Nr | SPIi | SPIr)

In the PQ version, a pre-shared key PPK is included in the computation.
 SKEYSEED = prf(Ni | Nr, g^ir)
    {SK_d' | SK_ai | SK_ar | SK_ei | SK_er | SK_pi' | SK_pr'}
                    = prf+ (SKEYSEED, Ni | Nr | SPIi | SPIr)


    SK_d  = prf+ (PPK, SK_d')
    SK_pi = prf+ (PPK, SK_pi')
    SK_pr = prf+ (PPK, SK_pr')

# Modeling

In the following model, we remove multiple layers of integrity and encryption, keeping the minimal required for the authentication and real or random.

*******************************************************************************)
set timeout=4.
set postQuantumSound = true.

hash h

(* pre-shared keys *)
name psk : message

(* long term keys *)
name skI : message
name skR : message


(* DDH randomnesses *)
name xi :  index ->  message
name xr :  index ->  message

abstract g : message
abstract exp : message -> message -> message

(* fresh randomness *)
name Ni : index ->   message
name Nr : index ->   message

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

process Initiator(i:index) =
  out(cI, <exp(g,xi(i)), Ni(i)>);

  in(cI, m);



  SI : out(cI,sign(  < exp(g,xi(i))
               , <Ni(i),
                  <snd(m)(*Nr*),
                   prfp(  hseed( <<Ni(i),snd(m)(*Nr*)>,  exp(fst(m),xi(i))>, seedpubkey )(* SKEYSEED *),
                        <Ni(i),snd(m)(*Nr*)> )
                   >>>,  skI  )
     );
  in(cI,signed);
  if checksign( signed, pk(skR)) =
      < fst(m)(*gI*)
               , <snd(m)(*Nr*),
                  <Ni(i)(*Ni*),
                   prfp(  hseed( < <Ni(i),snd(m)(*Nr*)>,   exp(fst(m),xi(i))>, seedpubkey ) (* SKEYSEED *),
                  <Ni(i),snd(m)(*Nr*)> )
                   >>> then
     FI :  out(cR, ok).


process Responder(i:index) =
  in(cR,m);
  out(cR, <exp(g,xr(i)), Nr(i)>);

  in(cR, signed);
  if checksign( signed, pk(skI)) =
      < fst(m)(*gI*)
               , <snd(m)(*Ni*),
                  <Nr(i)(*Nr*),
                   prfp(  hseed(< <snd(m)(*Ni*),Nr(i)>,  exp(fst(m),xr(i))>, seedpubkey)(* SKEYSEED *),
                   <snd(m)(*Ni*),Nr(i)> )
                   >>> then
    SR:  out(cR,
      sign(  < exp(g,xr(i))
               , <Nr(i),
                  <snd(m)(*Ni*),
                   prfp(  hseed(<  <snd(m)(*Ni*),Nr(i)>,  exp(fst(m),xi(i))>,seedpubkey)(* SKEYSEED *),
                      <snd(m)(*Ni*),Nr(i)> )
                   >>>,  skR
)).





system  out(cI, seedpubkey); ((!_j R: Responder(j)) | (!_i I: Initiator(i))).

(*****************)
(* Security game *)


(* We simply reveal the keys in the end, they should be indistinguishable from perfect keys *)

name idealkeys : index -> index -> message

process InitiatorRoR(i:index) =
  out(cI, <exp(g,xi(i)), Ni(i)>);

  in(cI, m);



  out(cI,sign(  < exp(g,xi(i))
               , <Ni(i),
                  <snd(m)(*Nr*),
                   prfp(  hseed(< <Ni(i),snd(m)(*Nr*)>,  exp(fst(m),xi(i))>, seedpubkey)(* SKEYSEED *),
                        <Ni(i),snd(m)(*Nr*)> )
                   >>>,  skI  )
     );
  in(cI,signed);
  if checksign( signed, pk(skR)) =
      < fst(m)(*gI*)
               , <snd(m)(*Nr*),
                  <Ni(i)(*Ni*),
                   prfp(  hseed(<  <Ni(i),snd(m)(*Nr*)>,   exp(fst(m),xi(i))>,seedpubkey)(* SKEYSEED *),
                  <Ni(i),snd(m)(*Nr*)> )
                   >>> then
    FI :   out(cR,
    diff( prfd(hseed( < <Ni(i),snd(m)(*Nr*)>,   exp(fst(m),xi(i))>,seedpubkey)(* SKEYSEED *),psk),
       try find jf such that  snd(m) = Nr(jf) in
	 idealkeys(jf,i)
       else fail)
       ).


process ResponderRor(i:index) =
  in(cR,m);
  out(cR, <exp(g,xr(i)), Nr(i)>);

  in(cR, signed);
  if checksign( signed, pk(skI)) =
      < fst(m)(*gI*)
               , <snd(m)(*Ni*),
                  <Nr(i)(*Nr*),
                   prfp(  hseed(< <snd(m)(*Ni*),Nr(i)>,  exp(fst(m),xr(i))>, seedpubkey)(* SKEYSEED *),
                   <snd(m)(*Ni*),Nr(i)> )
                   >>> then
    SR:  out(cR,
      sign(  < exp(g,xr(i))
               , <Nr(i),
                  <snd(m)(*Ni*),
                   prfp(  hseed(<  <snd(m)(*Ni*),Nr(i)>,  exp(fst(m),xi(i))>,seedpubkey)(* SKEYSEED *),
                      <snd(m)(*Ni*),Nr(i)> )
                   >>>,  skR
));

 FR : out(cR, diff( prfd(  hseed(<  <snd(m)(*Ni*),Nr(i)>,  exp(fst(m),xr(i))>,seedpubkey)(* SKEYSEED *), psk)
              ,        try find jf such that  snd(m) = Ni(jf) in
                    idealkeys(i,jf)
                        else fail)
).



system [core]  out(cI, seedpubkey); ((!_j R: ResponderRor(j)) | (!_i I: InitiatorRoR(i))).


goal [core] authI : forall (i:index),
       happens(FI(i)) => exec@FI(i) =>
           exists (j:index), SR(j) < FI(i) &&
                      fst(input@SI(i)) = exp(g,xr(j)) &&
                      snd(input@SI(i)) = Nr(j).
Proof.
intro i.
expand exec. expand cond.
euf H0.
exists j.
depends SI(i), FI(i).
case H1.
Qed.

goal [core] authR : forall (i:index),
       happens(FR(i)) => exec@FR(i) =>
           exists (j:index), SI(j) < FR(i) &&
                      fst(input@R(i)) = exp(g,xi(j)) &&
                      snd(input@R(i)) = Ni(j).
Proof.
intro i.
expand exec.
executable  pred(FR(i)).
depends  SR(i),FR(i).
use H1 with SR(i).
expand exec. expand cond.
euf H3.
exists i0.
case H0. depends R(i),FR(i).
Qed.

axiom [core] ddhcommu : forall (i,j:index), exp(exp(g,xi(i)),xr(j)) =  exp(exp(g,xr(j)),xi(i)) .

equiv [core] final.
Proof.

globalprf seq(il,jl->  prfd(  hseed( < <Ni(il),Nr(jl)>,  exp(exp(g,xr(jl)),xi(il))>, seedpubkey  )(* SKEYSEED *), psk)), news.


print.
rename seq(j,i -> n_PRF(j,i)), seq(j,i -> idealkeys(j,i)), ness.
print.

diffeq.

(* I part *)
forceuse authI with i.
case (try find jl,il such that
   hseed(<<Ni(i),snd(input@SI(i))>,exp(fst(input@SI(i)),xi(i))>,seedpubkey) =
   hseed(<<Ni(il),Nr(jl)>,exp(exp(g,xr(jl)),xi(il))>,seedpubkey)
 in idealkeys(jl,il)
 else
   prfd(hseed(<<Ni(i),snd(input@SI(i))>,exp(fst(input@SI(i)),xi(i))>,
        seedpubkey),psk)).
collision.
substeq Meq2.

case try find jf such that snd(input@SI(il)) = Nr(jf)
in idealkeys(jf,il) else fail.

substeq Meq4.

by use H2 with j.

by use H2 with j,i.


(* R part *)

forceuse authR with j.
case (try find jl,il such that
   hseed(<<snd(input@R(j)),Nr(j)>,exp(fst(input@R(j)),xr(j))>,seedpubkey) =
   hseed(<<Ni(il),Nr(jl)>,exp(exp(g,xr(jl)),xi(il))>,seedpubkey)
 in idealkeys(jl,il)
 else
   prfd(hseed(<<snd(input@R(j)),Nr(j)>,exp(fst(input@R(j)),xr(j))>,
        seedpubkey),psk)) .
substeq Meq2. substeq Meq2.

collision.

case try find jf such that snd(input@R(jl)) = Ni(jf) in idealkeys(jl,jf) else fail.
substeq Meq4. substeq Meq4.

by use H2 with il.

substeq snd(input@R(j)), Ni(j0).
substeq  fst(input@R(j)), exp(g,xi(j0)).

use H2 with j,j0.

forceuse ddhcommu with j0,j.
Qed.
