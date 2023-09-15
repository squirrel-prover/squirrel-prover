(**
# SIGNED DDH

The signed DDH protocol as described in [G] features two roles, P and S.
Each role is associated to a secret key (skP and skS).

* P -> S : <pk(skP), g^a>
* S -> P : <pk(skS),g^b>,sign(<<g^a,g^b>,pk(skP)>,skS)
* P -> S : sign(<<g^b,g^a>,pk(skS)>,skP)

We consider multiple sessions but two agents only (one agent for the role P and
one agent for the role S) and show the strong secrecy of the shared key.

* In this file `signed-ddh-P.sp`, we show that the key g^a^b as computed by P
  is indistinguishable from g^k with k fresh (system secretP).
* In another file `signed-ddh-S.sp`, we show that the key g^a^b as computed by S
  is indistinguishable from g^k with k fresh (system secretS).

[G] ISO/IEC 9798-3:2019, IT Security techniques – Entity authentication –
Part 3: Mechanisms using digital signature techniques.

*****************************************************************)

(**
We first declare some public constants, the secret keys for roles P and S,
the channels used by these two roles.
*)
abstract ok : message
abstract ko : message

name skP : message
name skS : message

channel cP
channel cS.

(**
Names `a` and `b` represent the random numbers used by roles P and S.
They are indexed so that each new session uses a new random name.
*)
name a : index -> message
name b : index -> message.
(**
The name `k` represents the random number used in the strong secrecy property.
It has 2 as index arity to model the fact that each interaction between
session `i` of role P and session `j` of role S uses a new random name.
*)
name k :  index * index -> message.

(**
We declare a DDH context, using `g` for the generator element and `^` for the
power operator.
*)
ddh g, (^) where group:message exponents:message.

(**
We also declare a signature scheme by specifying 3 function symbols.
*)
signature sign,checksign,pk.

(**
In the system `secretP`, we add an output at the end of the role of P.
This output is actually a bi-term:

* the left side of the system outputs the shared key as computed by P,
* the right side of the system outputs `g^k(i,j)` where `k(i,j)` is fresh.

The goal will be to prove that these two sides are indistinguishable.
*)
process Pchall(i:index) =
  out(cP, <pk(skP),g^a(i)>);
  in(cP, x2);
  let gS = snd(fst(x2)) in
  let pkS = fst(fst(x2)) in
  if checksign(<<g^a(i),gS>,pk(skP)>,snd(x2),pkS) && pkS = pk(skS) then
    (out(cP,sign(<<gS,g^a(i)>,pkS>,skP));
    in(cP, challenge);
      try find j such that gS = g^b(j) in
        out(cP, diff(g^a(i)^b(j),g^k(i,j)))
      else
        (** The `try find` construct is needed to retrieve the index `j`,
        but this else branch should never be reachable.
        We thus output a bi-term with distinct public constants so that
        the equivalence for the strong secrecy could not hold if this else
        branch is reached. *)
        out(cP, diff(ok,ko)))

process S(j:index) =
  in(cS, x1);
  let gP = snd(x1) in
  let pkP = fst(x1) in
  if pkP = pk(skP) then (
    out(cS, < <pk(skS),g^b(j)>, sign(<<gP,g^b(j)>,pkP>,skS)>);
    in(cS, x3);
    if checksign(<<g^b(j),gP>,pk(skS)>,x3,pkP) then
      out(cS,ok))

system (!_i Pchall(i) | !_j S(j)).

include Basic.

(**
In the proof of strong secrecy for the system `secretP`, we will use
the following property, stating that whenever P accepts a message from S,
this message is of the form `<<_,x>,_>` where `x = g^b(j)`.
*)
lemma  P_charac (i:index):
  happens(Pchall1(i)) =>
    cond@Pchall1(i) =>
      exists (j:index), snd(fst(input@Pchall1(i))) = g^b(j).
(**
The high-level idea of the proof is to use the EUF cryptographic axiom:
only S can forge a correct signature that will be accepted by P since
the secret key is not known by the attacker.
*)
Proof.
  (** We start by introducing the hypotheses and expanding the macros. *)
  intro Hap Hcond.
  expand cond, pkS(i)@Pchall1(i).
  destruct Hcond as [Meq Meq0].

  (** We then rewrite Meq using the message equality Meq0. *)
  rewrite Meq0 in Meq.
  (** We are now able to apply the `euf` tactic, which will search for
  occurences of signatures with `skS`: the only possibility is the output
  of an action `S(j)`.  *)
  euf Meq.
  (** The conclusion is now trivial from the Meq1 and D1 hypotheses. *)
   intro [j _].
  by exists j.
Qed.

(**
We now show the strong secrecy of the shared key for the system `secretP`,
expressed by the logic formula `forall t:timestamp, frame@t` where `frame@t`
is actually a bi-frame. We will prove that the left projection of `frame@t`
(_i.e._ where the shared key `g^a^b` is outputted) is indistinguishable from the
right projection of `frame@t` (_i.e._ where `g^k` is outputted).
*)
equiv strongSecP.
(**
The proof is done by induction, after having enriched the frame with some
additional (bi-)terms. Intuitively, the idea of enriching the frame is to
simplify the cases that are contexts built using applications of public
function symbols and terms added in the enriched frame.
It then remains to prove:

* the base case, _i.e._ prove that the enriched bi-frame is indistinguishable;
* the case corresponding to the output `diff(ok,ko)`, _i.e._ prove that this
output is never reached using the previous `P_charac` property.
*)
Proof.
  (** We start by enriching the frame. *)
  enrich
    skP, skS,
    seq(i:index =>g^a(i)),
    seq(j:index =>g^b(j)),
    seq(i,j:index =>diff( g ^ a(i), g) ^ diff( b(j), k(i,j))).

  (** We now apply the `induction` tactic, which generates several cases,
  one for each possible value that can be taken by the timestamp `t`.

  For most cases, applying the induction hypothesis `IH` allows to conclude
  because `frame@t` can be built from `frame@pred(t)` and elements added to
  the frame by the tactic `enrich`. *)
  induction t; try (by expandall; apply IH).

      (** Case where `t = init`.
      We use here the DDH assumption. *)
    + expandall.
      by ddh g,a,b,k.
    
      (** Case where `t = Pchall3(i)`.
      We will show that this case is not possible, by showing that the formula
      `exec@pred(Pchall3(i)) && cond@Pchall3(i)` is equivalent to `False`, relying
      on the previous property `P_charac`. *)
    + expand frame, exec, output.
      have ->: (exec@pred(Pchall3(i)) && cond@Pchall3(i)) <=> false. {
        split => //.
        intro [Hexec Hcond].
        expand cond.
        depends Pchall1(i), Pchall3(i) => //.
        intro Ord.
        executable pred(Pchall3(i)) => //. 
        intro Hexec'.
        use Hexec' with Pchall1(i) as Hexec1 => //.
        expand exec.
        use P_charac with i as [j0 Hyp] => //.
        by use Hcond with j0.
      }

      fa 5. fa 6.
      (** It now remains to simplify `if false then diff(ok,ko)`. *)
      by rewrite if_false.
Qed.
