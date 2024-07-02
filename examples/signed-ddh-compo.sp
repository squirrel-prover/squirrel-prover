(*******************************************************************************
SIGNED DDH

[G] ISO/IEC 9798-3:2019, IT Security techniques – Entity authentication –
Part 3: Mechanisms using digital signature techniques.

P -> S : <pk(kP), g^a>
S -> P : <pk(kS),g^b>,sign(<<g^a,g^b>,pk(kP)>,kS)
P -> S : sign(<<g^b,g^a>,pk(kS)>,kP)

We leverage the composition result of [1], to prove the security of a single
session in the presence of an adversary with access to a "backdoor" about the
signature function, which allows him to about signatures of some specific
messages.

It means that we only consider two session of the agents, P and S, using a1 and
b1 as DH shares. We consider that the other sessions of P (simulated thanks to
the oracle), use a(i) as a DH share, and b(i) for the other sessions of S.

The proof is split into two systems:

 - [auth] - which models the authentication property, i.e. that P and S must be
partnered with an honnest session of the protocol.

 - [secret] - which models the secrecy property. i.e. that if P and S are
partenered together, the derived key is real-or-random.  Those two properties
allow to conclude through the result of [1] the multi-session security of DDH.

[1] : Hubert Comon, Charlie Jacomme, and Guillaume Scerri. Oracle simula-
tion: a technique for protocol composition with long term shared secrets.
In Proceedings of the 2020 ACM SIGSAC Conference on Computer and
Communications Security, pages 1427–1444, 2020.
*******************************************************************************)

include Basic.

abstract ok : message
abstract ko : message

name kP : message
name kS : message

channel cP
channel cS

name a1 : message (* DH share of P *)
name b1 : message (* DH share of S *)
name k11 : message  (* ideal key derived between P and S *)
name a : index -> message
name b : index -> message

ddh g, (^) where group:message exponents:message.

signature sign,checksign,pk with oracle 
 forall (m:message,sk:message),
   (sk <> kP || exists (i:index, x1:message, x2:message), m=<<x1,g^a(i)>,x2> )
    &&
   (sk <> kS || exists (i:index, x1:message, x2:message), m=<<x1,g^b(i)>,x2>)

hash h

process P =
  out(cP, <pk(kP),g^a1>);
  in(cP, t);
  let gS = snd(fst(t)) in
  let pkS = fst(fst(t)) in
  if checksign(<<g^a1,gS>,pk(kP)>,snd(t),pkS) then
    out(cP,sign(<<gS,g^a1>,pkS>,kP));
    in(cP, challenge);
    if pkS= pk(kS) then
      if snd(fst(t)) = g^b1 then
        out(cP, ok)
      else
      (try find j such that snd(fst(t)) = g^b(j) in
        out(cP, ok)
      else
       out(cP, diff(ok,ko))
       )


process S =
  in(cS, sP);
  let gP = snd(sP) in
  let pkP = fst(sP) in
  out(cS, < <pk(kS),g^b1>, sign(<<gP,g^b1>,pkP>,kS)>);
  in(cS, signed);
  if checksign(<<g^b1,gP>,pk(kS)>,signed,pkP) then
    out(cS,ok);
    in(cS, challenge);
    if pkP=pk(kP) then
     if gP = g^a1 then
      out(cS, ok)
      else
       (try find l such that gP = g^a(l) in
          out(cS, ok)
	else
    	  out(cS, diff(ok,ko))
	 )


system auth = ( P | S).


process P2 =
  out(cP, <pk(kP),g^a1>);
  in(cP, t);
  let gS = snd(fst(t)) in
  let pkS = fst(fst(t)) in

  if checksign(<<g^a1,gS>,pk(kP)>,snd(t),pkS) then
    out(cP,sign(<<gS,g^a1>,pkS>,kP));
    in(cP, challenge);
    if pkS= pk(kS) then
      if snd(fst(t)) = g^b1 then
         out(cP, diff(g^a1^b1,g^k11))
      else
      (try find j such that snd(fst(t)) = g^b(j) in
         out(cP, g^a1^b(j)))

process S2 =
	in(cS, sP);
	let gP = snd(sP) in
	let pkP = fst(sP) in
	out(cS, < <pk(kS),g^b1>, sign(<<gP,g^b1>,pkP>,kS)>);
	in(cS, signed);
        if checksign(<<g^b1,gP>,pk(kS)>,signed,pkP) then
	out(cS,ok);
	in(cS, challenge);
	if pkP=pk(kP) then
          if gP = g^a1 then
            out(cS, diff(g^a1^b1,g^k11))
          else
            (try find l such that gP = g^a(l) in
               out(cP, g^b1^a(l)))

system secret = ( P2 | S2).

(** Prove that the condition above the only diff term inside S is never true. **)
lemma [auth] S1_charac :
  happens(S1,S4) => cond@S1 => (cond@S4 => False).
Proof.
  intro Hap Hcond1 Hcond4.
  expand cond, pkP. 
  destruct Hcond4 as [H1 H2 Meq].
  rewrite Meq in Hcond1.
  euf Hcond1.
    + intro [Hyp1 Hyp2].
      case Hyp1 => //.
      destruct Hyp1 as [i x1 x2 Hyp1].
      by use H1 with i.
    + auto.
Qed.


(** Prove that the condition above the only diff term inside P is never true. **)
lemma [auth] P1_charac :
   happens(P1,P4) => cond@P1 => (cond@P4 => False).
Proof.
  intro Hap Hcond1 Hcond4.
  expand cond.
  destruct Hcond4 as [H1 H2 Meq].
  rewrite /pkS Meq in *.
  euf Hcond1.
    + intro [Hyp1 Hyp2].
      case Hyp2 => //.
      destruct Hyp2 as [i x1 x2 Hyp2].
      by use H1 with i.
    + auto.
Qed.

(** The strong secrecy is directly obtained through ddh. *)
equiv [secret] secret.
Proof.
   ddh g, a1, b1, k11.
Qed.

(** The equivalence for authentication is obtained by using the unreachability
proofs over the two actions. The rest of the protocol can be handled through
some simple enriching of the induction hypothesis, and then dup applications. *)

equiv [auth] auth.
Proof.
   enrich kP, g^a1, g^b1, kS, seq(i:index => g^b(i)), seq(i:index => g^a(i)).

   induction t => //.

   + (* P *)
     expandall; by fa 6. 

   + (* P1 *)
     expandall; by fa 6.

   + (* P2 *)
     expandall; by fa 6.

   + (* P3 *)
     expandall; fa 6. by apply IH.

   + (* P4 *)
     expand frame, exec. fa 6.

     have ->: (exec@pred(P4) && cond@P4) <=> False.
     {split => //. intro [Hexec Hcond].
      depends P1, P4 => //. 
      executable pred(P4) => //.
      intro Hexec' Ord. 
      use Hexec' with P1 as H1 => //.
      expand exec.
      by use P1_charac.
     }

   by fa 7; rewrite if_false in 7.

   + (* A *)
     by expandall; fa 6.

   + (* A1 *)
      by expandall; fa 6.

   + (* S *)
     by expandall; fa 6.

   + (* S1 *)
     by expandall; fa 6.

   + (* S2 *)
     by expandall; fa 6.

   + (* S3 *)
     expandall. by apply IH.

   + (* S4 *)
     expand frame, exec.

     have ->: (exec@pred(S4) && cond@S4) <=> False.
     {split => //. intro [Hexec Hcond]. 
      depends S1, S4 => //.
      executable pred(S4) => //.
      intro Hexec' Ord.
      use Hexec' with S1 as H1 => //.
      expand exec.
      by use S1_charac.
     }

      by fa 6; fa 7; rewrite if_false in 7.

   + (* A2 *)
     by expandall; fa 6.

   + (* A3 *)
     by expandall; fa 6.
Qed.
