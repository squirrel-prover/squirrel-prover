(**
# SIGNED DDH

The signed DDH protocol as described in [G] features two roles, P and S.
Each role is associated to a secret key (skP and skS).

* P -> S : <pk(skP), g^a>
* S -> P : <pk(skS),g^b>,sign(<<g^a,g^b>,pk(skP)>,skS)
* P -> S : sign(<<g^b,g^a>,pk(skS)>,skP)

We consider multiple sessions but two agents only (one agent for the role P and
one agent for the role S) and show the strong secrecy of the shared key.

* In this file `signed-ddh-S.sp`, we show that the key g^a^b as computed by S
  is indistinguishable from g^k with k fresh (system secretS).
* In another file `signed-ddh-P.sp`, we show that the key g^a^b as computed by P
  is indistinguishable from g^k with k fresh (system secretP).

[G] ISO/IEC 9798-3:2019, IT Security techniques – Entity authentication –
Part 3: Mechanisms using digital signature techniques.

*******************************************************************************)

(**
Declarations are identical to the ones in `signed-ddh-P.sp`.
*)
abstract ok : message
abstract ko : message

name skP : message
name skS : message

channel cP
channel cS

name a : index -> message
name b : index -> message
name k : index * index -> message.

ddh g, (^) where group:message exponents:message.

signature sign,checksign,pk

(**
The system `secretS` is the counterpart of the system `secretP` defined in
the file `signed-ddh-P.sp`.

This time, we add an output at the end of the role of S.
*)
process P(i:index) =
  out(cP, <pk(skP),g^a(i)>);
  in(cP, x2);
  let gs = snd(fst(x2)) in
  let pks = fst(fst(x2)) in
  if checksign(<<g^a(i),gs>,pk(skP)>,snd(x2),pks) && pks = pk(skS) then
    out(cP,sign(<<gs,g^a(i)>,pks>,skP))

process Schall(j:index) =
  in(cS, x1);
  let gp = snd(x1) in
  let pkp = fst(x1) in
  if pkp = pk(skP) then (
    out(cS, < <pk(skS),g^b(j)>, sign(<<gp,g^b(j)>,pkp>,skS)>);
    in(cS, x3);
    if checksign(<<g^b(j),gp>,pk(skS)>,x3,pkp) then (
      out(cS,ok);
      in(cS, challenge);
      try find i such that gp = g^a(i) in
        (out(cS, diff(g^a(i)^b(j),g^k(i,j))))
      else
        out(cS, diff(ok,ko))))

system  (!_i P(i) | !_j Schall(j)).

include Basic.

(**
In the proof of strong secrecy for the system `secretS`, we will use
the following property, stating that whenever S accepts a message from P,
this message is of the form `<<_,x>,_>` where `x = g^a(i)`.
*)
lemma  S_charac (j:index):
  happens(Schall1(j)) =>
    exec@Schall1(j) =>
      exists (i:index), snd(input@Schall(j)) = g^a(i).
Proof.
  intro Hap Hexec.
  executable pred(Schall1(j)) => //.
  depends Schall(j), Schall1(j) => //.
  intro Ord Hexec'.
  use Hexec' with Schall(j) as Hyp => //.
  expand exec, cond, pkp(j)@Schall1(j).
  assert fst(input@Schall(j)) = pk(skP) as Meq' => //.
  rewrite Meq' in Hexec. destruct Hexec as [Hexec Hcheck].
  euf Hcheck.
  intro [i _].
  by exists i.
Qed.

(**
We show the counterpart of the property `strongSecP`, this time for the
system `secretS`. The proof is carried out exactly in the same way.
*)
equiv strongSecS.
Proof.
  enrich
    skP, skS,
    seq(i:index =>g^a(i)),
    seq(j:index =>g^b(j)),
    seq(i,j:index =>diff( g ^ a(i), g) ^ diff( b(j), k(i,j))).

  induction t; try (by expandall; apply IH).

    + (* init *)
      expandall.
      by ddh g,a,b,k.

    + (* Schall3 *)
      expand frame, exec, output.
      have ->: (exec@pred(Schall3(j)) && cond@Schall3(j)) <=> False.
      {split => //. 
       intro [Hexec Hcond].
       expand cond.
       depends Schall1(j), Schall3(j) => //.
       intro Ord.
       executable pred(Schall3(j)) => //.
       intro Hexec'.
       use Hexec' with Schall1(j) as Hexec1 => //.
       expand exec.
       use S_charac with j as [j0 Hyp] => //.
       by use Hcond with j0. 
      }

  fa 5. fa 6.
  by rewrite if_false.
Qed.
