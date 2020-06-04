(*******************************************************************************
SSH (WITH FORWARDING AGENT)

[H] Hubert Comon, Charlie Jacomme, and Guillaume Scerri. Oracle simula-
tion: a technique for protocol composition with long term shared secrets.
In Jonathan Katz and Giovanni Vigna, editors, Proceedings of the 27st
ACM Conference on Computer and Communications Security (CCS’20),
Orlando, USA, November 2020. ACM Press. To appear

P -> S : g^a
S -> P : g^b, pkS, sign(h(g^a,g^b, g^ab),skS) )
P -> S : enc( sign(g(g^a,g^b,g^ab),skP) , g^ab)

Second part of the proof of ssh with a modified agent forwarding. It
corresponds to the security a the forwarded SSH key exchange, but with oracles
that allow to simulate all other forwarded SSH login and previous non forwarded
SSH logins.
*******************************************************************************)

abstract ok : message
abstract ko : message
abstract forwarded : message
abstract reqsign : message
abstract anssign : message

name kP : message
name kS : message

channel cP
channel cS

name ake1 : index -> message
name bke1 : index -> message
name ake11 : message
name bke11 : message
name k11 : message

name a1 : message
name b1 : message
name c11 : message
name a : index -> message
name b : index -> message
name k : index -> index -> message

(* We only use the fact that an IND-CCA1 encryption is unforgeable. Due to
   limitation of the tool, we model the symmetric encryption as an asymmetric
   encryption. Remark that the symmetric encryption must be euf even when a hash
   containing the key is given. In other words, the hash function h should be
   PRF. *)
signature enc,checkdec,pke
abstract dec : message -> message -> message

hash h
name hKey : message

axiom [auth] collres : forall (m1,m2:message), h(m1, hKey) = h(m2, hKey) => m1 = m2
axiom [auth] hashnotpair : forall (m1,m2:message), forall (m:message), m1 = h(m, hKey) => fst(m1) <> m2

axiom [auth] freshindex : exists (l:index), True

axiom DDHinj : forall (m1,m2:message), m1 <> m2 => g^m1 <> g^m2
axiom DDHcommut : forall (m1,m2:message), g^m1^m2 = g^m2^m1


signature sign,checksign,pk with oracle forall (m:message,sk:message)
(sk <> kP
 || exists (i:index, m1:message, m2:message)
      m = <forwarded, h(<<g^a(i),m1>,m2>, hKey)> (* O_FPS *)
 || exists (i:index, m1:message, m2:message)
      m = h(<<g^ake1(i),m1>,m2>, hKey) (* O_KE1 *)
 )
  &&
(sk <> kS
 || exists (i:index, m1:message, m2:message)
      m = <forwarded, h(<<m1,g^b(i)>,m2>, hKey)> (* O_FPS *)
 || exists (i:index, m1:message, m2:message)
      m = h(<<m1,g^bke1(i)>,m2>, hKey) (* O_KE1 *)
)

axiom [auth] signnottag :
  forall (m1,m2:message),
  fst(sign(m1,m2)) <> anssign &&
  fst(sign(m1,m2)) <> reqsign

axiom [auth] difftags :
  anssign <> forwarded &&
  forwarded <> reqsign && reqsign <> anssign

(** We first present the general SSH process. *)

process P1FA =
  in(cP,gB);
  out(cP,ok);
  (* begin P1 *)
  in(cP,t);
  let sidP = h(<<g^ake11,gB>,pke(k11)>, hKey) in
  let pkS = fst(t) in
  if pkS = pk(kS) && checksign(snd(t),pkS) = sidP then
  out(cP, enc(sign(sidP,kP),pke(k11)));
  (* end P1 *)

  (* begin FA *)
  !_i (
    in(cP,y);
    let x = dec(y,pke(k11)) in
    if checkdec(y,pke(k11)) = x then
    if fst(x) = reqsign then
    out(cP, enc(<anssign, sign(<forwarded,snd(x)>,kP)>,pke(k11)))
  )

process PDIS =
  (* begin S0 *)
  in(cS, gP0);
  out(cS, g^bke11);
  (* end S0 *)
  (* begin S1 *)
  in(cS,garbage);
  let sidS0 = h(<<gP0,g^bke11>,pke(k11)>, hKey) in
  out(cS, <<pk(kS),g^bke11>,sign(sidS0, kS)>);
  in(cS, encP );
  if checksign(dec(encP,gP0^bke11),pk(kP)) = sidS0 then
      out(cS,ok);
  (* end S1 *)
  (* begin Pdis0 *)
  out(cP, g^a1);
  in(cP, gB);
  (* end Pdis0 *)
  out(cP,ok);
  (* begin Pdis1 *)
  in(cP,t);
  let sidP = h(<<g^a1,gB>,gB^a1>, hKey) in
  let pkS = fst(t) in
  if pkS = pk(kS) && checksign(snd(t),pkS) = sidP then
    out(cP, enc( <reqsign, sidP>,k11));
    in(cP, signans);
    let y = dec(signans,pke(k11)) in
    if checkdec(signans,pke(k11)) = y then
    if fst(y) = anssign then
    Pok: out(cP, enc(snd(y),gB^a1))


process SDIS =
  (* begin SDIS0 *)
  in(cS, gP);
  out(cS, g^b1);
  (* end SDIS0 *)

  (* begin SDIS1 *)
  in(cS,garbage);
  let sidS = h(<<gP,g^b1>,gP^b1>, hKey) in
  out(cS, <<pk(kS),g^b1>,sign(sidS, kS)>);
  in(cS, encP );
  if checksign(dec(encP,gP^b1),pk(kP)) = <forwarded,sidS> then
    Sok : out(cS,ok)

system [fullSSH] (P1FA | SDIS | PDIS).

(* Now the process for the secrecy *)

process P1FADDH =
  in(cP,gB);
  out(cP,ok);
  (* begin P1 *)
  in(cP,t);
  let sidP = h(<<g^ake11,gB>,pke(k11)>, hKey) in
  let pkS = fst(t) in
  if pkS = pk(kS) && checksign(snd(t),pkS) = sidP then
  out(cP, enc(sign(sidP,kP),k11));
  (* end P1 *)

  (* begin FA *)
  !_i (
    in(cP,y);
    let x2= dec(y,pke(k11)) in
    if checkdec(y,pke(k11)) = x2 then
    if fst(x2) = reqsign then
    out(cP, enc(<anssign, sign(<forwarded,snd(x2)>,kP)>,k11))
  )

process PDISDDH =
  (* begin S0 *)
  in(cS, gP0);
  out(cS, g^bke11);
  (* end S0 *)
  (* begin S1 *)
  in(cS,garbage);
  let sidS0 = h(<<gP0,g^bke11>,pke(k11)>, hKey) in
  out(cS, <<pk(kS),g^bke11>,sign(sidS0, kS)>);
  in(cS, encP );
  if checksign(dec(encP,gP0^bke11),pk(kP)) = sidS0 then
  out(cS,ok);
  (* end S1 *)
  (* begin Pdis0 *)
  out(cP, g^a1);
  in(cP, gB);
  (* end Pdis0 *)
  if gB = g^b1 then
  out(cP,diff(g^a1^b1,g^c11))


process SDISDDH =
  (* begin SDIS0 *)
  in(cS, gP);
  out(cS, g^b1);
  (* end SDIS0 *)

  (* begin SDIS1 *)
  if gP = g^a1 then
  out(cP,diff(g^a1^b1,g^c11))

system [secret] (P1FADDH | SDISDDH | PDISDDH).


equiv [left,secret] [right,secret] secret.
Proof.
   ddh a1, b1, c11.
Qed.


(** And now the authentication process. *)

process P1FAauth =
  in(cP,gB);
  out(cP,ok);
  (* begin P1 *)
  in(cP,t);
  let sidPaF = h(<<g^ake11,gB>,pke(k11)>, hKey) in
  let pkSaF = fst(t) in
  if pkSaF = pk(kS) && checksign(snd(t),pkS) = sidPaF then
  out(cP, enc(sign(sidPaF,kP),k11));
  (* end P1 *)

  (* begin FA *)
  !_i (
    in(cP,y3);
    let x3 = dec(y3,pke(k11)) in
    if checkdec(y3,pke(k11)) = x3 then
    if fst(x3) = reqsign then
    out(cP, enc(<anssign, sign(<forwarded,snd(x3)>,kP)>,k11))
  )

process PDISauth =
  (* begin S0 *)
  in(cS, gP0);
  out(cS, g^bke11);
  (* end S0 *)
  (* begin S1 *)
  in(cS,garbage);
  let sidS0a = h(<<gP0,g^bke11>,pke(k11)>, hKey) in
  out(cS, <<pk(kS),g^bke11>,sign(sidS0a, kS)>);
  in(cS, encP );
  if checksign(dec(encP,gP0^bke11),pk(kP)) = sidS0a then
  out(cS,ok);
  (* end S1 *)
  (* begin Pdis0 *)
  out(cP, g^a1);
  in(cP, gB);
  (* end Pdis0 *)
  out(cP,ok);
  (* begin Pdis1 *)

  in(cP,t);
  let sidPa = h(<<g^a1,gB>,gB^a1>, hKey) in
  let pkSa = fst(t) in
  if pkSa = pk(kS) && checksign(snd(t),pkSa) = sidPa then
  out(cP, enc( <reqsign, sidPa>,k11));
  in(cP, signans);
  let ya = dec(signans,pke(k11)) in
  if checkdec(signans,pke(k11)) = ya then
  if fst(ya) = anssign then
  out(cP, enc(snd(ya),gB^a1));
  in(cP,challenge);
  try find i such that
    gB = g^b(i) || gB = g^b1 || gB=g^bke1(i) || gB = g^bke11
  in out(cP,ok)
  else Pfail : out(cP,diff(ok,ko))


process SDISauth =
  (* begin SDIS0 *)
  in(cS, gP);
  out(cS, g^b1);
  (* end SDIS0 *)

  (* begin SDIS1 *)
  in(cS,garbage);
  let sidSa = h(<<gP,g^b1>,gP^b1>, hKey) in
  out(cS, <<pk(kS),g^b1>,sign(sidSa, kS)>);
  in(cS, encP );
  if checksign(dec(encP,gP^b1),pk(kP)) = <forwarded,sidSa> then
    out(cS,ok);
    in(cS,challenge);
    try find i such that gP = g^a(i) || gP = g^a1 in
      out(cS,ok)
    else
      Sfail :  out(cS,diff(ok,ko))

system [auth] ( P1FAauth | SDISauth | PDISauth).


goal [none, auth] P_charac :
  exec@PDIS5 => (cond@Pfail => False) .
Proof.
  expand exec@PDIS5.
  expand cond@PDIS5; expand cond@Pfail.
  substitute pkSa@PDIS5,pk(kS).
  euf M0.

  (* oracle case *)
  case H3.
  case H3.
  apply hashnotpair to sidPa@PDIS5, forwarded.
  apply H3 to <<g^a1,input@PDIS4>,input@PDIS4^a1>.
  apply signnottag to sidPa@P2, kP.
  apply H1 to i1.
  left; right.
  apply collres  to <<m2,g^bke1(i1)>,m3> ,<<g^a1,input@PDIS4>,input@PDIS4^a1>.

  (* honest case SDIS *)
  apply collres  to <<input@SDIS,g^b1>,input@SDIS^b1> ,<<g^a1,input@PDIS4>,input@PDIS4^a1>.
  apply freshindex.
  apply H1 to l.

  apply freshindex.
  apply H1 to l.
  right.
  apply collres  to <<input@PDIS,g^bke11>,pke(k11)>,<<g^a1,input@PDIS4>,input@PDIS4^a1>.

Qed.


(* This is the most complex case, as the received signature was not performed by PDis, but queried by PDis to FA. *)
goal [none, auth] S_charac :
   exec@Sok =>(cond@Sfail => False).
Proof.
  expand exec@Sok; expand cond@Sok; expand cond@Sfail.

  euf M0.

(* oracle clase *)

  case H2.
  case H3.
(* sub case with wrong tag *)
  apply H1 to i.
  apply collres to <<input@SDIS,g^b1>,input@SDIS^b1>, <<g^a(i),m>,m1>.

  apply hashnotpair to  h(<<g^ake1(i1),m2>,m3>, hKey), forwarded.
(* Here, I do weird stuff, else we have an assert false in completion.ml. TODO *)
  apply H3 to <<g^ake1(i1),m2>,m3>.

(* else, it comes from P2, and is not well tagged *)
  apply hashnotpair to  sidPaF@P2, forwarded.
  apply H3 to (<<g^ake11,input@P1>,pke(k11)>).

(* Honest case of signature produced by Fa.
   We need to prove that the sign req received by FA comes from PDIS. *)

  executable pred(Sok).
  assert P3(i) <= Sok.
  case H2.
  depends SDIS, Sok.
  apply H3 to P3(i).
  expand exec@P3(i).
  expand cond@P3(i).

(* We have that x3 is a message encrypted with the secret key, we use the euf of encryption *)
  euf M2.

(* Ill-tagged cases *)
  apply signnottag to sidPaF@P2,kP.
  apply difftags.

(* Honest case *)
  assert PDIS5 <= Sok.
  case H5.
  apply H3 to PDIS5.
  expand exec@PDIS5.
  expand cond@PDIS5.
  apply H1 to i.
  right.
  apply collres to <<input@SDIS,g^b1>,input@SDIS^b1>, <<g^a1,input@PDIS4>,input@PDIS4^a1>.
Qed.

(* The equivalence for authentication is obtained by using the unreachability
   proofs over the two actions. The rest of the protocol can be handled through
   some simple enriching of the induction hypothesis, and then dup applications. *)

equiv [left, auth] [right, auth] auth.
Proof.
  enrich a1; enrich b1; enrich seq(i-> b(i)); enrich seq(i-> a(i)); enrich kP; enrich kS;
  enrich ake11; enrich bke11; enrich seq(i-> bke1(i)); enrich seq(i-> ake1(i)); enrich k11; enrich hKey.

  induction t.

  expandall.
  fa 12.

  expandall.
  fa 12.

  expandall.
  fa 12.

  expandall.
  fa 12.

  expandall.
  fa 12.

  expandall.
  fa 12.

  expandall.
  fa 12.

  expandall.
  fa 12.

  expandall.
  fa 12.

  expandall.
  fa 12.
  expand seq(i -> a(i)),i.


  expand frame@Sfail.
  equivalent exec@Sfail, false.

  apply S_charac.
  depends Sok, Sfail.
  executable Sfail.
  apply H1 to Sok.
  expand exec@Sfail.

  fa 12. fa 13. noif 13.

  expandall.
  fa 12.

  expandall.
  fa 12.

  expandall.
  fa 12.

  expandall.
  fa 12.

  expandall.
  fa 12.

  expandall.
  fa 12.

  expandall.
  fa 12.

  expandall.
  fa 12.

  expandall.
  fa 12.
  expand seq(i -> b(i)),i. expand seq(i -> bke1(i)),i.

  expand frame@Pfail.
  equivalent exec@Pfail, false.

  apply P_charac.
  depends PDIS5, Pfail.
  executable Pfail.
  apply H1 to PDIS5.
  expand exec@Pfail.

  fa 12. fa 13. noif 13.

  expandall.
  fa 12.

  expandall.
  fa 12.

  expandall.
  fa 12.

  expandall.
  fa 12.
Qed.
