(*******************************************************************************
SIGNED DDH

[G] ISO/IEC 9798-3:2019, IT Security techniques – Entity authentication –
Part 3: Mechanisms using digital signature techniques.

P -> S : <pk(kP), g^a>
S -> P : <pk(kS),g^b>,sign(<<g^a,g^b>,pk(kP)>,kS)
P -> S : sign(<<g^b,g^a>,pk(kS)>,kP)

We consider multiple sessions but two agents only: each agent playing his own role.
1/ We analyse whether the key as computed by P is indistinguishable from g^k with k fresh (system secretP).
2/ We analyse whether the key as computed by S is indistinguishable from g^k with k fresh (system secretS).
*******************************************************************************)

abstract ok : message
abstract ko : message

name skP : message
name skS : message

channel cP
channel cS

ddh g, (^) where group:message exposants:message.

name a : index -> message
name b : index -> message
name k :  index -> index -> message

signature sign,checksign,pk

process Pchall(i:index) =
  out(cP, <pk(skP),g^a(i)>);
  in(cP, t);
  let gS = snd(fst(t)) in
  let pkS = fst(fst(t)) in
  if checksign(snd(t),pkS) = <<g^a(i),gS>,pk(skP)> && pkS = pk(skS) then
    out(cP,sign(<<gS,g^a(i)>,pkS>,skP));
    in(cP, challenge);
     try find j such that gS = g^b(j) in
      out(cP, diff(g^a(i)^b(j),g^k(i,j)))
       else
      out(cP, diff(ok,ko))
  else null

process S(i:index) =
  in(cS, sP);
  let gP = snd(sP) in
  let pkP = fst(sP) in
  if pkP = pk(skP) then
  out(cS, < <pk(skS),g^b(i)>, sign(<<gP,g^b(i)>,pkP>,skS)>);
  in(cS, signed);
  if checksign(signed,pkP) = <<g^b(i),gP>,pk(skS)> then
    out(cS,ok)


system [secretP] (!_i Pchall(i) | !_j S(j)).


process P(i:index) =
  out(cP, <pk(skP),g^a(i)>);
  in(cP, t);
  let gs = snd(fst(t)) in
  let pks = fst(fst(t)) in
  if checksign(snd(t),pks) = <<g^a(i),gs>,pk(skP)> && pks = pk(skS) then
    out(cP,sign(<<gs,g^a(i)>,pks>,skP))


process Schall(i:index) =
  in(cS, sP);
  let gp = snd(sP) in
  let pkp = fst(sP) in
  if fst(sP) = pk(skP) then
  out(cS, < <pk(skS),g^b(i)>, sign(<<gp,g^b(i)>,pkp>,skS)>);
  in(cS, signed);
  if checksign(signed,pkp) = <<g^b(i),gp>,pk(skS)> then
    out(cS,ok);
    in(cS, challenge);
      try find l such that gp = g^a(l) in
      out(cS, diff(g^a(l)^b(i),g^k(l,i)))
      else out(cS, diff(ok,ko))
  else null

system [secretS] (!_i P(i) | !_j Schall(j)).


goal [secretP] P_charac (i:index):
 happens(Pchall1(i)) => 
 cond@Pchall1(i) => 
 exists (j:index), snd(fst(input@Pchall1(i))) = g^b(j).
Proof.
  simpl.
  expand cond, pkS(i)@Pchall1(i).
  rewrite Meq0 in Meq. 
  euf Meq.
  exists j.
Qed.

goal [secretS] S_charac (r:index):
 happens(S1(r)) =>
 exec@S1(r) => exists (s:index), snd(input@S(r)) = g^a(s).
Proof.
  simpl.
  expand exec.
  executable pred(S1(r)).
  depends S(r), S1(r).
  use H1 with S(r).
  expand exec, cond.
  expand pkp(r)@S1(r).
  rewrite Meq in *.
  euf H0.
  by exists i.
Qed.



equiv [secretS] strongSecS.
Proof.
    enrich skP, skS, seq(i:index ->g^a(i)), seq(i:index ->g^b(i)),
           seq(i,j:index ->diff(g^a(i)^b(j),g^k(i,j))).

    induction t; try (by expandall; apply IH).

    (* init *)
    expandall.
    by ddh g,a,b,k.

    (* Schall3 *)
    expand frame, exec, output.


    equivalent exec@pred(Schall3(j)) && cond@Schall3(j), False.
    expand cond.
    executable pred(Schall3(j)).
    depends S1(j), Schall3(j).
    use H2 with S1(j).
    use S_charac with j.
    by use H1 with s.

    fa 5.
    fa 6.
    by noif 6.
Qed.



equiv [secretP] strongSecP.
Proof.
    enrich skP, skS, seq(i:index ->g^a(i)), seq(i:index ->g^b(i)),
           seq(i,j:index ->diff(g^a(i)^b(j),g^k(i,j))).

    induction t; try (by expandall; apply IH).

    (* init *)
    expandall.
    by ddh g,a,b,k.

    (* Pchall3 *)
    expand frame, exec, output.


    equivalent exec@pred(Pchall3(i)) && cond@Pchall3(i), False.
    expand cond.
    executable pred(Pchall3(i)).
    depends Pchall1(i), Pchall3(i).
    use H2 with Pchall1(i).
    expand exec.
    use P_charac with i.
    by use H1 with j.

    fa 5.
    fa 6.
    by noif 6.
Qed.
