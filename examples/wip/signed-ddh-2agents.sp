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

hash h

abstract ok : message
abstract ko : message

name skP : message
name skS : message

channel cP
channel cS

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
  (* si je remplace ci-dessus fst(sP) par pkp, j'obtiens une erreur etrange *)
  (* [error> Error in new input at line 1 char 142  
   before ")": Symbol pks used with arity 0, but defined with arity 1. *)
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


goal [none,secretP] P_charac :
  forall (i:index), cond@Pchall1(i) => exists (j:index), snd(fst(input@Pchall1(i))) = g^b(j).
Proof.
  simpl.
  expand cond@Pchall1(i).
  expand pkS(i)@Pchall1(i).  
  substitute fst(fst(input@Pchall1(i))), pk(skS).
  euf M0.
  exists j. 
Qed.

goal [none, secretS] S_charac :
  forall (r:index), exec@S1(r) => exists (s:index), snd(input@S(r)) = g^a(s).
Proof.
  simpl.
  expand exec@S1(r). 
  executable pred(S1(r)).  
  depends S(r), S1(r).
  apply H2 to S(r).   
  expand exec@S(r).
  expand cond@S(r).
  expand cond@S1(r).
  expand pkp(r)@S1(r).
  substitute  fst(input@S(r)), pk(skP).
  euf M0.
  exists i.
Qed.



equiv [left,secretS] [right,secretS] strongSecS.
Proof.
    enrich skP. 
    enrich skS. 
    enrich seq(i->g^a(i)).
    enrich seq(i->g^b(i)).
    enrich seq(i,j->diff(g^a(i)^b(j),g^k(i,j))).

    induction t.

    (* init *)
    expandall.
    ddh a,b,k.
    (* Pchall *)
    expandall.
    expand seq(i->g^a(i)), i.
    fa 6.
    (* Pchall1 *)
    expandall.
    expand seq(i->g^a(i)), i.
    fa 6.   
    (* A *)
    expandall.
    expand  seq(i->g^a(i)), i.
    fa 6.
    (* S *)
    expandall.
    expand  seq(i->g^b(i)), j.
    fa 6.
    (* S1 *)
    expandall.
    expand  seq(i->g^b(i)), j.
    fa 6.
    (* Case Schall2 *)
    expandall.
    expand  seq(i->g^a(i)), l.
    expand seq(i->g^b(i)), j.
    expand seq(i,j->(diff(g^a(i)^b(j), g^k(i,j)))), l, j.
    fa 8.    
    (* Schall3 *)
    expand frame@Schall3(j).
    expand exec@Schall3(j).
    expand output@Schall3(j).


    equivalent exec@pred(Schall3(j)) && cond@Schall3(j), False.
    expand cond@Schall3(j).
    executable pred(Schall3(j)).
    depends S1(j), Schall3(j).
    apply H2 to S1(j).
    apply S_charac to j.
    apply H1 to s.

    fa 5.
    fa 6.
    noif 6.   
    (* A1 *)
    expandall.
    expand  seq(i->g^b(i)), j.
    fa 6.
    (* A2 *)
     expandall.
     fa 5.
Qed.






equiv [left,secretP] [right,secretP] strongSecP.
Proof.
    enrich skP. 
    enrich skS. 
    enrich seq(i->g^a(i)).
    enrich seq(i->g^b(i)).
    enrich seq(i,j->diff(g^a(i)^b(j),g^k(i,j))).

    induction t.

    (* init *)
    expandall.
    ddh a,b,k.
    (* Pchall *)
    expandall.
    expand seq(i->g^a(i)), i.
    fa 6.
    (* Pchall1 *)
    expandall.
    expand seq(i->g^a(i)), i.
    fa 6.   
    (* Case Pchall2 *)
    expandall.
    expand  seq(i->g^a(i)), i.
    expand seq(i->g^b(i)), j.
    expand seq(i,j->(diff(g^a(i)^b(j), g^k(i,j)))), i, j.
    fa 8.    
    (* Pchall3 *)
    expand frame@Pchall3(i).
    expand exec@Pchall3(i).
    expand output@Pchall3(i).


    equivalent exec@pred(Pchall3(i)) && cond@Pchall3(i), False.
    expand cond@Pchall3(i).
    executable pred(Pchall3(i)).
    depends Pchall1(i), Pchall3(i).
    apply H2 to Pchall1(i).
    expand exec@Pchall1(i).
    apply P_charac to i.
    apply H1 to j.

    fa 5.
    fa 6.
    noif 6.
    (* A *)
    expandall.
    expand  seq(i->g^a(i)), i.
    fa 6.
    (* S *)
    expandall.
    expand  seq(i->g^b(i)), j.
    fa 6.
    (* S1 *)
    expandall.
    expand  seq(i->g^b(i)), j.
    fa 6.
    (* A1 *)
    expandall.
    expand  seq(i->g^b(i)), j.
    fa 6.
    (* A2 *)
     expandall.
     fa 5.
Qed.



