(*******************************************************************************
SIGNED DDH

[G] ISO/IEC 9798-3:2019, IT Security techniques – Entity authentication –
Part 3: Mechanisms using digital signature techniques.

P -> S : g^a
S -> P : <g^a,g^b>,h(<g^a,g^b>,kS)
P -> S : h(<g^a,g^b>,kP)
*******************************************************************************)

hash h

abstract ok : message
abstract ko : message

name kP : message
name kS : message

channel cP
channel cS

name a : index -> message
name b : index -> message
name k : index -> index -> message

term test : boolean = zero

process P(i:index) =
  out(cP, g^a(i));
  in(cP, t);
  let hash_share = snd(t) in
  let gb = snd(fst(t)) in
  if h(<g^a(i),gb>,kS) = snd(t) then
    out(cP, h(<g^a(i),gb>,kP));
    in(cP, challenge);
    try find j such that gb = g^b(j) in
      out(cP, diff(g^a(i)^b(j),g^k(i,j)))
    else
      out(cP, diff(ok,ko))
  else null

process S(i:index) =
  in(cS, ga);
  out(cS, < <ga,g^b(i)>, h(<ga,g^b(i)>,kS)>);
  in(cS, hash_shares);
  if hash_shares = h(<ga,g^b(i)>,kP) then
    out(cS,ok);
    in(cS, challenge);
    try find l such that ga = g^a(l) in
      out(cS, diff(g^a(l)^b(i),g^k(l,i)))
    else
      out(cS, diff(ok,ko))
  else null

system (!_i P(i) | !_j S(j)).

(* Show that condition S1 implies the next one. *)
goal S1_charac :
  forall (r:index),
  cond@S1(r) =>
  exists (s:index),
  input@S(r) = g^a(s).
Proof.
  simpl.
  expand cond@S1(r).
  euf M0.
  exists i.
Qed.

(* Show that condition P1 implies the next one. *)
goal P1_charac :
  forall (r:index),
cond@P1(r) =>
  exists (s:index),
  snd(fst(input@P1(r))) = g^b(s).
Proof.
  simpl.
  expand cond@P1(r).
  euf M0.
  exists j.
Qed.

equiv unreach.
Proof.
    enrich kP; 
    enrich kS; 
    enrich seq(i->g^a(i));
    enrich seq(i->g^b(i)); 
    enrich seq(i,j->diff(g^a(i)^b(j),g^k(i,j))).

    induction t.

    expandall.
    ddh a, b, k.

   (* Case P *)
    expandall.
    expand  seq(i->g^a(i)), i.
    fa 6.

  (* Case P1 *)
   expandall.
   expand  seq(i->g^a(i)), i.
   fa 6.

  (* Case P2 *)
   expandall.
   expand  seq(i->g^a(i)), i.
   expand seq(i->g^b(i)), j.
   expand seq(i,j->(diff(g^a(i)^b(j), g^k(i,j)))), i, j.
   fa 8.

   (* Case P3 *)
   expand frame@P3(i); expand exec@P3(i); expand output@P3(i).
   equivalent exec@pred(P3(i)) && cond@P3(i), False.
   expand cond@P3(i).
   executable pred(P3(i)).

   depends P1(i), P3(i).
   apply H2 to P1(i).
   expand exec@P1(i).
   apply P1_charac to i.
   apply H1 to s.

   fa 5. 
   noif 6.

   (* Case A *)
   expandall.
   expand  seq(i->g^a(i)), i.
   fa 6.

   (* Case S *)
   expandall.
   expand  seq(i->g^b(i)), j.
   fa 6.

   (* Case S1 *)
   expandall.
   expand  seq(i->g^b(i)), j.
   fa 6.

   (* Case S2 *)
   expandall.
   expand  seq(i->g^a(i)), l;
   expand seq(i,j->(diff(g^a(i)^b(j), g^k(i,j)))), l, j.
   fa 7.

   (* Case S3 *)
   expand frame@S3(j); expand exec@S3(j).
   equivalent exec@pred(S3(j)) && cond@S3(j), False.
   expand cond@S3(j).
   executable pred(S3(j)).
   depends S1(j), S3(j).
   apply H2 to S1(j).
   expand exec@S1(j).
   apply S1_charac to j.
   apply H1 to s.

   fa 5.
   noif 6.

   (* Case A1 *)
   expandall.
   expand  seq(i->g^b(i)), j.
   fa 6.

Qed.
