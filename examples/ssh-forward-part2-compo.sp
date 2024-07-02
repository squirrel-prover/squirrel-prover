(*******************************************************************************
SSH (WITH FORWARDING AGENT)

We refer to P and S as the two processes of ssh-forward-part1-comp.sp

In this protocol,

 - PFA is a process which first runs P, and then starts a forwarded agent
process, which accepts to sign queries received on the secure channel
established through P

 - PDIS is a protocol which first runs S, and then can run P on the distant
server. When P while require a signature, it will request it on the channel
established by S, to contact some forwarded agent.

 - SDIS is the server that will communicated with P run by PDIS.


PFA <-> PDIS : SSH key exchange, deriving an ideal key k11.

PDIS -> SDIS : g^a
SDIS-> PDIS : g^b, pkS, sign(h(g^a,g^b, g^ab),skS) )
PDIS -> PFA : enc(<"sign request",h(g^a,g^b, g^ab)>,k11 )
PFA -> PDIS : enc(<"sign answer",sign(h(g^a,g^b, g^ab),skP)>,k11 )
PDIS -> SDIS : enc( sign(g(g^a,g^b,g^ab),skP) , g^ab)


We prove that one session of the second key exchange is secure, when it is using
a secure channel with an idealized key k11, and the attacker has access to an
oracle that allows to simulate either other sessions of the forwarded key
exchange, or sessions of the original key exchange.

This proof, is split into authentication and secrecy, as in
ssh-forward-part1-comp.sp.

The security of a forwarded session when using a previously derived key is
proved in the file ssh-forward-part2-compo.sp. Together with [1], those two
files prove the security of SSH with one session forwarding for an unbounded
number of sessions.

[1] : Hubert Comon, Charlie Jacomme, and Guillaume Scerri. Oracle simula-
tion: a technique for protocol composition with long term shared secrets.
In Proceedings of the 2020 ACM SIGSAC Conference on Computer and
Communications Security, pages 1427–1444, 2020.
*******************************************************************************)

set timeout=4.

include Basic.

abstract ok : message
abstract ko : message
abstract forwarded : message
abstract reqsign : message
abstract anssign : message

name kP : message
name kS : message

channel cP
channel cS
channel c

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
name k : index * index -> message.

name r : message
name r2 : index -> message
name r3 : message
name r4 : message
name r5 : message

ddh g, (^) where group:message exponents:message.

(* As ssh uses a non keyed hash function, we rely on a fixed key hKey known to the attacker *)
(* Note that hKey has to be a name and not a constant and this key is revealed at the beginning *)

name hKey : message
hash h with oracle forall (m:message,sk:message), sk = hKey

(* We assume that the encryption is INT-CTXT. This is assumed to hold even when the key appears under some hash functions. *)
senc enc,dec with hash h.


signature sign,checksign,pk with oracle forall (m:message,sk:message),
(sk <> kP
 || exists (i:index, m1:message, m2:message),
      m = <forwarded, h(<<g^a(i),m1>,m2>, hKey)> (* O_FPS *)
 || exists (i:index, m1:message, m2:message),
      m = h(<<g^ake1(i),m1>,m2>, hKey) (* O_KE1 *)
 )
  &&
(sk <> kS
 || exists (i:index, m1:message, m2:message),
      m = <forwarded, h(<<m1,g^b(i)>,m2>, hKey)> (* O_FPS *)
 || exists (i:index, m1:message, m2:message),
      m = h(<<m1,g^bke1(i)>,m2>, hKey) (* O_KE1 *)
)


(** We first present the general SSH process. *)

process P1FA =
  in(cP,gB);
  out(cP,ok);
  (* begin P1 *)
  in(cP,t);
  let sidP = h(<<g^ake11,gB>,k11>, hKey) in
  let pkS = fst(t) in
  if pkS = pk(kS) && checksign(sidP, snd(t), pkS) then (
  out(cP, enc(sign(sidP,kP),r,k11));
  (* end P1 *)

  (* begin FA *)
  !_i (
    in(cP,y);
    let x = dec(y,k11) in
    if x <> fail then (
    if fst(x) = reqsign then (
    out(cP, enc(<anssign, sign(<forwarded,snd(x)>,kP)>,r2(i),k11))
  )))).

process PDIS =
  (* begin S0 *)
  in(cS, gP0);
  out(cS, g^bke11);
  (* end S0 *)
  (* begin S1 *)
  in(cS,garbage);
  let sidS0 = h(<<gP0,g^bke11>,k11>, hKey) in
  out(cS, <<pk(kS),g^bke11>,sign(sidS0, kS)>);
  in(cS, encP );
  if checksign(sidS0, dec(encP,gP0^bke11), pk(kP)) then (
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
  if pkS = pk(kS) && checksign(sidP, snd(t),pkS) then (
    out(cP, enc( <reqsign, sidP>,r3,k11));
    in(cP, signans);
    let y = dec(signans,k11) in
    if y <> fail then (
    if fst(y) = anssign then (
    Pok: out(cP, enc(snd(y),r4,gB^a1)))))).


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
  let x = dec(encP,gP^b1) in
  if checksign(<forwarded, sidS>, x, pk(kP)) then
    Sok : out(cS,ok).

system fullSSH = (P1FA | SDIS | PDIS).

(* Now the process for the secrecy *)

process P1FADDH =
  in(cP,gB);
  out(cP,ok);
  (* begin P1 *)
  in(cP,t);
  let sidP = h(<<g^ake11,gB>,k11>, hKey) in
  let pkS = fst(t) in
  if pkS = pk(kS) && checksign(sidP, snd(t), pkS) then (
  out(cP, enc(sign(sidP,kP),r,k11));
  (* end P1 *)

  (* begin FA *)
  !_i (
    in(cP,y);
    let x2= dec(y,k11) in
    if x2 <> fail then
    if fst(x2) = reqsign then
    out(cP, enc(<anssign, sign(<forwarded,snd(x2)>,kP)>,r2(i),k11))
  )).

process PDISDDH =
  (* begin S0 *)
  in(cS, gP0);
  out(cS, g^bke11);
  (* end S0 *)
  (* begin S1 *)
  in(cS,garbage);
  let sidS0 = h(<<gP0,g^bke11>,k11>, hKey) in
  out(cS, <<pk(kS),g^bke11>,sign(sidS0, kS)>);
  in(cS, encP );
  if checksign(sidS0, dec(encP,gP0^bke11), pk(kP)) then (
  out(cS,ok);
  (* end S1 *)
  (* begin Pdis0 *)
  out(cP, g^a1);
  in(cP, gB);
  (* end Pdis0 *)
  if gB = g^b1 then
  out(cP,diff(g^a1^b1,g^c11))).


process SDISDDH =
  (* begin SDIS0 *)
  in(cS, gP);
  out(cS, g^b1);
  (* end SDIS0 *)

  (* begin SDIS1 *)
  if gP = g^a1 then (
  out(cP,diff(g^a1^b1,g^c11))).

system secret = (P1FADDH | SDISDDH | PDISDDH).


equiv [secret] secret.
Proof.
   ddh g, a1, b1, c11.
Qed.


(** And now the authentication process. *)

process P1FAauth =
  in(cP,gB);
  out(cP,ok);
  (* begin P1 *)
  in(cP,t);
  let sidPaF = h(<<g^ake11,gB>,k11>, hKey) in
  let pkSaF = fst(t) in
  if pkSaF = pk(kS) && checksign(sidPaF, snd(t), pkS) then (
  out(cP, enc(sign(sidPaF,kP),r,k11));
  (* end P1 *)

  (* begin FA *)
  !_i (
    in(cP,y3);
    let x3 = dec(y3,k11) in
    if x3 <> fail then
    if fst(x3) = reqsign then
    out(cP, enc(<anssign, sign(<forwarded,snd(x3)>,kP)>,r2(i),k11))
  )).

process PDISauth =
  (* begin S0 *)
  in(cS, gP1);
  out(cS, g^bke11);
  (* end S0 *)
  (* begin S1 *)
  in(cS,garbage);
  let sidS0a = h(<<gP1,g^bke11>,k11>, hKey) in
  out(cS, <<pk(kS),g^bke11>,sign(sidS0a, kS)>);
  in(cS, encP );
  if checksign(sidS0a, dec(encP,gP1^bke11), pk(kP)) then (
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
  if pkSa = pk(kS) && checksign(sidPa, snd(t), pkSa) then (
  out(cP, enc( <reqsign, sidPa>,r3,k11));
  in(cP, signans);
  let ya = dec(signans,k11) in
  if ya <> fail then (
  if fst(ya) = anssign then (
  out(cP, enc(snd(ya),r4,gB^a1));
  in(cP,challenge);
  try find i such that (
    gB = g^b(i) || gB = g^b1 || gB=g^bke1(i) || gB = g^bke11)
  in (out(cP,ok))
  else (Pfail : out(cP,diff(ok,ko))))))).


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
  let x4 = dec(encP,gP^b1) in
  if checksign(<forwarded, sidSa>, x4, pk(kP)) then (
    out(cS,ok);
    in(cS,challenge);
    try find i such that (gP = g^a(i) || gP = g^a1) in
      (out(cS,ok))
    else (
      Sfail :  out(cS,diff(ok,ko))))

system auth = ( P1FAauth | SDISauth | PDISauth).


(* Based on a difference between the bitstring lengths, we can assume that it is
impossible to confuse a hash with the tag forwarded, and another hash. *)

axiom [auth] hashlengthnotpair (m1,m2:message):
   <forwarded,h(m1,hKey)> <> h(m2, hKey)

(* The following axiom is a modelling trick. We need at some point to use an
hypothesis that require to instantiate an index, but this index is not used. *)
axiom [auth] freshindex : exists (l:index), True

axiom [auth] signnottag (m1,m2:message):
  fst(sign(m1,m2)) <> anssign &&
  fst(sign(m1,m2)) <> reqsign

axiom [auth] difftags :
  anssign <> forwarded &&
  forwarded <> reqsign && reqsign <> anssign.



lemma [auth] P_charac :
  happens(Pfail) => exec@PDIS5 => (cond@Pfail => False) .
Proof.
  intro Hap He Hc.
  depends PDIS5, Pfail => // Hap2.
  expand exec, cond.
  destruct He as [_ [He Hchk]].
  rewrite !He in *.
  expand sidPa.
  euf Hchk.

    + (* oracle case *)
      intro Euf. destruct Euf as [_ [_|[i m m1 [H1|[i1 H2]]]]] => //.
        - by use hashlengthnotpair with
          <<m,g^b(i)>,m1>, <<g^a1,input@PDIS4>,input@PDIS4^a1> as HH.
     
        - use signnottag with sidPa@P2, kP.
          use Hc with i1 => //.
          destruct H2 as [m2 m3 H2]. 
          right; right.
          by collision.

    + (* honest case SDIS *)
      intro [Euf Heq].
      use freshindex as [l _].
      use Hc with l => //.
      by case Euf; expand sidSa; collision => _.

    + intro [Euf Heq].
      use freshindex as [l _].
      use Hc with l => //.
      right.
      by case Euf; expand sidS3; collision => _.
Qed.


(* This is the most complex case, as the received signature was not performed by PDis, but queried by PDis to FA. *)
lemma [auth] S_charac :
   happens(Sfail) => exec@Sok =>(cond@Sfail => False).
Proof.
  intro Hap He Hc.
  depends Sok, Sfail => // Hap2.
  expand exec, cond.
  destruct He as [_ Hchk].

  expand sidSa, x4.
  euf Hchk.

  + (* oracle case *)
    intro Euf. destruct Euf as [[_|[i m m1 H1]] H2]=> //.
    destruct H1 as [H1| [i1 m2 m3 H1]].
      - (* sub case with wrong tag *)
        use Hc with i => //.
        assert h(<<input@SDIS,g^b1>,input@SDIS^b1>,hKey) = h(<<g^a(i),m>,m1>,hKey) => //.
        by collision.
      - by use hashlengthnotpair with <<input@SDIS,g^b1>,input@SDIS^b1>, <<g^ake1(i1),m2>,m3>.

  + (* else, it comes from P2, and is not well tagged *)
    intro [Euf _].
    by use hashlengthnotpair with
    <<input@SDIS,g^b1>,input@SDIS^b1>, <<g^ake11,input@P1>,k11> as Hlen;
    intro *; case Euf; expand sidPaF.

  + (* Honest case of signature produced by Fa.
    We need to prove that the sign req received by FA comes from PDIS. *)
    intro [i [Euf Meq]].
    assert forall t, t < Sok => exec@t as H2. {
      intro t Ht.
      by apply exec_le (pred(Sok)).
    }.
    depends SDIS, Sok => // _.
    have _: happens(SDIS); 1: auto.
    have _: happens(P3(i)); 1: case Euf; auto.
    expand x3(i)@P3(i).
    use H2 with P3(i) as H3; 2: case Euf; auto.
    expand exec, cond.
    destruct H3 as [H3 [Mneq Meq0]].

    assert (x3(i)@P3(i) = dec(input@P3(i),k11)) as D1 => //.
    (* We have that x3 is a message encrypted with the secret key, we use the intctxt of encryption *)
    intctxt D1 => //.
      - (* Ill-tagged case 1 *)
         by use signnottag with sidPaF@P2,kP. 
      - (* Ill-tagged case 2 *)
        by use difftags.
      - (* Honest case *)
        intro [H4 Meq1].
        assert happens(PDIS5) as U; 1: by case Euf.
        expand x3(i)@P3(i), sidPa.
        assert PDIS5 <= Sok;
        1: by case Euf.
        use H2 with PDIS5; 2: by auto.
        expand exec, cond.
        use Hc with i => //.
        right.
        expand pkSa, sidPa.
        assert (h(<<g^a1,input@PDIS4>,input@PDIS4^a1>,hKey) =
          h(<<input@SDIS,g^b1>,input@SDIS^b1>,hKey)) as Hcol => //.
        collision => [[A _] _].
        by rewrite A.
Qed.

(* The equivalence for authentication is obtained by using the unreachability
   proofs over the two actions. The rest of the protocol can be handled through
   some simple enriching of the induction hypothesis, and then dup applications. *)

equiv [auth] auth.
Proof.
  enrich a1, b1, seq(i:index => b(i)), seq(i:index => a(i)), kP, kS;
  enrich ake11, bke11, seq(i:index => bke1(i)), seq(i:index => ake1(i)), k11, hKey, r,
   seq(i:index =>r2(i)), r3, r4, r5.

  induction t; try (expandall; apply IH).

  + (* Init *)
    auto.

  + (* Sfail *)
     expand frame.
     have -> : exec@Sfail <=> false. {
       split => //.
       intro Hfail.
       use S_charac => //.
       - depends Sok, Sfail => // _.
         by apply exec_le Sfail. 
       - rewrite /exec // in Hfail. 
     }
     by rewrite if_false in 17.

  + (* Pfail *)
    expand frame.
    have -> : exec@Pfail <=> false. {
      split => //.
      intro Hfail.
      use P_charac; try auto.
      - depends PDIS5, Pfail => // _.
        by apply exec_le Pfail.
       - rewrite /exec // in Hfail.
  }
  by rewrite if_false in 17.
Qed.
