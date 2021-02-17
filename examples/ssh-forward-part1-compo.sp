(*******************************************************************************
SSH

Original version:

P -> S : g^a
S -> P : g^b, pkS, sign(h(g^a,g^b, g^ab),skS) )
P -> S : enc( sign(g(g^a,g^b,g^ab),skP) , g^ab)

This protocol instantiate a key exchange, where the derived key is already used
inside the key exchange. This corresponds to the so called "key confirmation"
process. We leverage the composition results of [1] to prove the security of the
SSH protocol. This is done by proving the security of a single session of SSH,
while giving access to an oracle to the attacker, that allows him to simulate
either other honnest sessions of SSH, or other forwarded session.

As this protocol is a confirmation, we have to prove that

 * just after the key is derived, it satisfies the real-or-random property,
cf. system [secret]

 * if the key confirmation succeeds, two honnest sessions are paired together,
cf. system [auth].

For the first point, we actually split the first message of S into two messages,
yielding the protocol:

P -> S : g^a
S -> P : g^b
S -> P:  pkS, sign(h(g^a,g^b, g^ab),skS) )
P -> S : enc( sign(g(g^a,g^b,g^ab),skP) , g^ab)


The security of a forwarded session when using a previously derived key is
proved in the file ssh-forward-part2-compo.sp. Together with [1], those two
files prove the security of SSH with one session forwarding for an unbounded
number of sessions.


[1] : Hubert Comon, Charlie Jacomme, and Guillaume Scerri. Oracle simula-
tion: a technique for protocol composition with long term shared secrets.
In Proceedings of the 2020 ACM SIGSAC Conference on Computer and
Communications Security, pages 1427–1444, 2020.
*******************************************************************************)

abstract ok : message
abstract ko : message
abstract forwarded : message

name kP : message
name kS : message

channel cP
channel cS
channel c

name a1 : message
name b1 : message
name k11 : message
name a : index -> message
name b : index -> message
name k : index -> index -> message

abstract enc : message -> message -> message
abstract dec : message -> message -> message


(* As ssh uses a non keyed hash function, we rely on a fixed key hKey known to the attacker *)
(* Note that hKey has to be a name and not a constant and the attacker can compute h values with the oracle.  *)

name hKey : message
hash h with oracle forall (m:message,sk:message), sk = hKey


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
  out(cS, <pk(kS),sign(sidS, kS)>);
  in(cS, encP );
  if checksign(dec(encP,gP^b1),pk(kP)) = sidS then
    Sok : out(cS,ok)

system [fullSSH] K: ( P | S).

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
  out(cS, <pk(kS),sign(sidS, kS)>);
  in(cS, encP );
  if checksign(dec(encP,gP^b1),pk(kP)) = sidS then
      out(cS,ok);
     in(cS,challenge);
     try find i such that gP = g^a(i) || gP = g^a1 in
         out(cS,ok)
     else
       Sfail :  out(cS,diff(ok,ko))

system [auth]  K: (Pauth | Sauth).

axiom [auth] hashnotfor :
  forall (x1,x2:message), h(x1,hKey) <> <forwarded,x2>

(* This is an axiom that simply states the existence of an index *)
axiom [auth] freshindex : exists (l:index), True.


(** Prove that the condition above the only diff term inside S is never true. **)
goal [none, auth] P_charac :
  cond@Pok => (cond@Pfail => False) .
Proof.
  simpl.
  expand cond@Pok;expand cond@Pfail; expand pkS1@Pok.
  substitute fst(input@Pok), pk(kS).
  euf Meq0.
  expand sidP@Pok.
  case H1.
  case H1.

  collision.

  by use H0 with i.

  by use hashnotfor with <<g^a1,input@P1>,input@P1^a1>, x2.

  collision.

  use freshindex.
  use H0 with l.
Qed.

(** Prove that the condition above the only diff term inside P is never true. **)
goal [none, auth] S_charac :
  cond@Sok => (cond@Sfail => False).
Proof.
  intro *.
  expand cond@Sok; expand cond@Sfail.
  euf H.

  case H1.
  case H1.
  use H0 with i.

  by collision.

  by use hashnotfor with <<input@S,g^b1>,input@S^b1>, x2.

  collision.
  use freshindex.
  use H0 with l.
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

   (* P *)
   expandall; fa 7.
   (* P1 *)
   expandall; fa 7.
   (* Pok *)
   expandall; fa 7.
   (* Pauth3 *)
   expandall; fa 7.
   expand seq(i->g^b(i)),i.
   (* Pfail *)
   expand frame@Pfail.

   equivalent exec@Pfail, False.
   expand exec@Pfail.
   executable pred(Pfail).
   depends Pok, Pfail.
   use H1 with Pok.
   expand exec@Pok.
   by use P_charac.

   fa 7; fa 8.
   by noif 8.

   (* A *)
   by expandall; fa 7.

   (* S *)
   by expandall; fa 7.

   (* S1 *)
   by expandall; fa 7.

   (* Sok *)
   by expandall; fa 7.

   (* Sauth3 *)
   expandall; fa 7.
   expand seq(i->g^a(i)),i.
   (* Safil *)
   expand frame@Sfail.

   equivalent exec@Sfail, False.
   expand exec@Sfail.
   executable pred(Sfail).
   depends Sok, Sfail.
   use H1 with Sok.
   expand exec@Sok.
   by use S_charac.

   fa 7; fa 8.
   by noif 8.

   (* A1 *)
   by expandall; fa 7.
Qed.
