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
cf. system secret

 * if the key confirmation succeeds, two honnest sessions are paired together,
cf. system auth.

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

include Basic.

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
name k : index * index -> message

abstract enc : message * message -> message
abstract dec : message * message -> message

ddh g, (^) where group:message exponents:message.

(* As ssh uses a non keyed hash function, we rely on a fixed key hKey known to the attacker *)
(* Note that hKey has to be a name and not a constant and the attacker can compute h values with the oracle.  *)

name hKey : message
hash h with oracle forall (m:message,sk:message), sk = hKey


signature sign,checksign,pk with oracle forall (m:message,sk:message),
(sk <> kP
 || exists (i:index, x1:message, x2:message), m=h(<<g^a(i),x1>,x2>, hKey) (* O_PS *)
 || exists (x:message), m=<forwarded,x> )  (* O_forward *)
  &&
(sk <> kS
 || exists (i:index, x1:message, x2:message), m=h(<<x1,g^b(i)>,x2>, hKey) (* O_PS *)
 || exists (x:message), m=<forwarded,x> ) (* O_forward) *)


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
  if pkS = pk(kS) && checksign(sidP, snd(t), pkS) then
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
  if checksign(sidS, dec(encP,gP^b1), pk(kP)) then
    Sok : out(cS,ok)

system fullSSH = ( P | S).

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


system secret = (PDDH | SDDH).


(** The strong secrecy is directly obtained through ddh. *)
equiv [secret] secret.
Proof.
   ddh g, a1, b1, k11.
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
  if pkS = pk(kS) && checksign(sidP, snd(t), pkS) then
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
  if checksign(sidS, dec(encP,gP^b1), pk(kP)) then
      out(cS,ok);
     in(cS,challenge);
     try find i such that gP = g^a(i) || gP = g^a1 in
         out(cS,ok)
     else
       Sfail :  out(cS,diff(ok,ko))

system auth = (Pauth | Sauth).

axiom [auth] hashnotfor (x1,x2:message): h(x1,hKey) <> <forwarded,x2>

(* This is an axiom that simply states the existence of an index *)
axiom [auth] freshindex : exists (l:index), True.


(** Prove that the condition above the only diff term inside S is never true. **)
lemma [auth] P_charac :
  happens(Pfail) => cond@Pok => (cond@Pfail => False) .
Proof.
  intro Hap HcOk HcFail.
  depends Pok, Pfail => // _.
  expand cond, pkS1.
  destruct HcOk as [Hpk HcOk].
  rewrite !Hpk in HcOk.
  euf HcOk.
    + intro Euf. destruct Euf as [H [_|[i x1 x2 H1]]]; 1: by auto.
      expand sidP1; destruct H1 as [_|[x3 H1]].

        - collision => _; use HcFail with i => //.

        - by use hashnotfor with <<g^a1,input@P1>,input@P1^a1>, x3.

    + intro [Euf Heq].
      expand sidP1. case Euf. 
      - expand sidS1. collision => _.
        use freshindex as [l _].
        use HcFail with l => //.
      - expand sidS1. collision => _.
        use freshindex as [l _].
        use HcFail with l => //.
Qed.

(** Prove that the condition above the only diff term inside P is never true. **)
lemma [auth] S_charac :
  happens(Sfail) => cond@Sok => (cond@Sfail => False).
Proof.
  intro Hap HcOk HcFail.
  depends Sok, Sfail => // _.
  expand cond.
  expand sidS1; euf HcOk.

    + intro Euf. destruct Euf as [[_|H1] H2]; 1: by auto.
      destruct H1 as [i x x1 [_|[x2 H1]]].

       - use HcFail with i => //.
         by collision.

       - by use hashnotfor with <<input@S,g^b1>,input@S^b1>, x2.

    + intro [Euf _]; case Euf.
        - expand sidP1; collision => _; use freshindex as [l _]; use HcFail with l => //.
        - expand sidP1; collision => _; use freshindex as [l _]; use HcFail with l => //.
Qed.


(** The equivalence for authentication is obtained by using the unreachability
proofs over the two actions. The rest of the protocol can be handled through
some simple enriching of the induction hypothesis, and then dup applications. *)

equiv [auth] auth.
Proof.
   enrich a1, b1, seq(i:index => g^b(i)), seq(i:index => g^a(i)), kP, kS, hKey.

   induction t; try (by expandall; apply IH).

   + (* init *)
     auto.

   + (* Pfail *)
     expand frame.

     have -> : exec@Pfail <=> false. {
       expand exec.
       split; 2: by auto => _.
       depends Pok, Pfail => // _.
       executable pred(Pfail); 1,2: by auto.
       intro He; use He with Pok; 2: by auto.
       
       expand exec.
       by use P_charac.
     }

     by rewrite if_false in 7.

   + (* Sfail *)
     expand frame.

     have -> : exec@Sfail <=> False. {
       expand exec.
       split; 2: by auto => _.
       depends Sok, Sfail => // _.
       executable pred(Sfail); 1,2: by auto.
       intro He; use He with Sok; 2: by auto.
       
       expand exec.
       by use S_charac.
     }

     by rewrite if_false in 7.

Qed.
