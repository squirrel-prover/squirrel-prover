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

First part of the proof of ssh with a modified agent forwarding. It
corresponds to the security a the basic SSH key exchange, but with oracles that
allow to simulate all other honest logins, and the forwarded SSH logins.
*******************************************************************************)

abstract ok : message
abstract ko : message
abstract forwarded : message

name kP : message
name kS : message

channel cP
channel cS

name a1 : message
name b1 : message
name k11 : message
name a : index -> message
name b : index -> message
name k : index -> index -> message

abstract enc : message -> message -> message
abstract dec : message -> message -> message

axiom encdec : forall (x1,x2:message), dec(enc(x1,x2),x2) = x1

hash h
name hKey : message

axiom [auth] hashnotfor :
  forall (x1,x2:message), h(x1,hKey) <> <forwarded,x2>

axiom [auth] collres :
  forall (x1,x2:message), h(x1,hKey) = h(x2,hKey) => x1=x2

axiom [auth] freshindex : exists (l:index), True

axiom DDHinj : forall (x1,x2:message), x1 <> x2 => g^x1 <> g^x2
axiom DDHcommut : forall (x1,x2:message), g^x1^x2 = g^x2^x1


signature sign,checksign,pk with oracle forall (m:message,sk:message)
(sk <> kP
 || exists (i:index, x1:message, x2:message) m=h(<<g^a(i),x1>,x2>, hKey) (* O_PS *)
 || exists (x:message) m=<forwarded,x> )  (* O_forward *)
  &&
(sk <> kS
 || exists (i:index, x1:message, x2:message) m=h(<<x1,g^b(i)>,x2>, hKey) (* O_PS *)
 || exists (x:message) m=<forwarded,x> ) (* O_forward) *)


(** We first present the general ssh process. *)

process P =
 (* begin P0 *)
  out(cP, g^a1);
  in(cP, gB);
 (* end P0 *)
  out(cP,ok);
 (* begin P1 *)

  in(cP,t);
  let sidP = h(<<g^a1,gB>,gB^a1>, hKey) in
  let pkS = fst(t) in
  if pkS = pk(kS) && checksign(snd(t),pkS) = sidP then
    Pok : out(cP, enc(sign(sidP,kP),gB^a1))


process S =
 (* begin S0 *)
  in(cS, gP);
  out(cS, g^b1);
 (* end S0 *)

  (* begin S1 *)
  in(cS,garbage);
  let sidS = h(<<gP,g^b1>,gP^b1>, hKey) in
  out(cS, <<pk(kS),g^b1>,sign(sidS, kS)>);
  in(cS, encP );
  if checksign(dec(encP,gP^b1),pk(kP)) = sidS then
    Sok : out(cS,ok)

system [fullSSH] ( P | S).

(* The secret is expected to hold at the end of P0 *)

process PDDH =
 (* begin P0 *)
  out(cP, g^a1);
  in(cP, gB);
 (* end P0 *)
  if gB = g^b1 then
     out(cP,diff(g^a1^b1,g^k11))

process SDDH =
 (* begin S0 *)
  in(cS, gP);
  out(cS, g^b1);
 (* end S0 *)
  if gP = g^a1 then
     out(cP,diff(g^a1^b1,g^k11))


system [secret] (PDDH | SDDH).


(** The strong secrecy is directly obtained through ddh. *)
equiv [left,secret] [right,secret] secret.
Proof.
   ddh a1, b1, k11.
Qed.


(** The authentication says that the key confirmation must fail in case of misauthentication *)

process Pauth =
 (* begin P0 *)
  out(cP, g^a1);
  in(cP, gB);
 (* end P0 *)
  out(cP,ok);
 (* begin P1 *)

  in(cP,t);
  let sidP = h(<<g^a1,gB>,gB^a1>, hKey) in
  let pkS = fst(t) in
  if pkS = pk(kS) && checksign(snd(t),pkS) = sidP then
     out(cP, enc(sign(sidP,kP),gB^a1));
     in(cP,challenge);
     try find i such that gB = g^b(i) || gB = g^b1 in
         out(cP,ok)
     else
        Pfail : out(cP,diff(ok,ko))

process Sauth =
 (* begin S0 *)
  in(cS, gP);
  out(cS, g^b1);
 (* end S0 *)

  (* begin S1 *)
  in(cS,garbage);
  let sidS = h(<<gP,g^b1>,gP^b1>, hKey) in
  out(cS, <<pk(kS),g^b1>,sign(sidS, kS)>);
  in(cS, encP );
  if checksign(dec(encP,gP^b1),pk(kP)) = sidS then
      out(cS,ok);
     in(cS,challenge);
     try find i such that gP = g^a(i) || gP = g^a1 in
         out(cS,ok)
     else
       Sfail :  out(cS,diff(ok,ko))

system [auth] ( Pauth | Sauth).



(** Prove that the condition above the only diff term inside S is never true. **)
goal [none, auth] P_charac :
  cond@Pok => (cond@Pfail => False) .
Proof.
  simpl.
  expand cond@Pok.
  expand cond@Pfail.
  expand pkS@Pok.
  substitute fst(input@Pok), pk(kS).
  euf M0.
  expand sidP@Pok.
  case H2.
  case H2.

  apply collres to <<g^a1,input@P1>,input@P1^a1>, <<x,g^b(i)>,x1>.
  apply H0 to i.

  apply hashnotfor to <<g^a1,input@P1>,input@P1^a1>, x2.

  apply collres to <<g^a1,input@P1>,input@P1^a1>,<<input@S,g^b1>,input@S^b1>.

  apply freshindex.
  apply H0 to l.
Qed.

(** Prove that the condition above the only diff term inside P is never true. **)
goal [none, auth] S_charac :
  cond@Sok => (cond@Sfail => False).
Proof.
  simpl.
  expand cond@Sok; expand cond@Sfail.
  euf M0.

  case H1.
  case H2.
  apply H0 to i.
  apply collres to <<g^a(i),x>,x1>,<<input@S,g^b1>,input@S^b1>.

  apply hashnotfor to <<input@S,g^b1>,input@S^b1>, x2.

  apply collres to <<g^a1,input@P1>,input@P1^a1>,<<input@S,g^b1>,input@S^b1>.
  apply freshindex.
  apply H0 to l.
Qed.


(** The equivalence for authentication is obtained by using the unreachability
proofs over the two actions. The rest of the protocol can be handled through
some simple enriching of the induction hypothesis, and then dup applications. *)

equiv [left, auth] [right, auth] auth.
Proof.
   enrich a1; enrich b1;
   enrich seq(i-> b(i)); enrich seq(i-> a(i));
   enrich kP; enrich kS; enrich hKey.

   induction t.

   expandall.
   fa 7.

   expandall.
   fa 7.

   expandall.
   fa 7.

   expandall.
   fa 7.
   expand seq(i->g^b(i)),i.

   expand frame@Pfail.
   equivalent exec@Pfail, False.
   expand exec@Pfail.
   executable pred(Pfail).
   depends Pok, Pfail.
   apply H2 to Pok.
   expand exec@Pok.
   apply P_charac.
   fa 7. fa 8.
   noif 8.

   expandall.
   fa 7.

   expandall.
   fa 7.

   expandall.
   fa 7.

   expandall.
   fa 7.

   expandall.
   fa 7.
   expand seq(i->g^a(i)),i.

   expand frame@Sfail.
   equivalent exec@Sfail, False.
   expand exec@Sfail.
   executable pred(Sfail).
   depends Sok, Sfail.
   apply H2 to Sok.
   expand exec@Sok.
   apply S_charac.
   fa 7. fa 8.
   noif 8.

   expandall.
   fa 7.
Qed.