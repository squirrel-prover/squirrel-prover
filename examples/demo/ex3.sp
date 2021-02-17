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

process P(i:index) =
  out(cP, g^a(i));
  in(cP, t);
  let hash_share = snd(t) in
  let gb = snd(fst(t)) in
  if h(<g^a(i),gb>,kS) = snd(t) then
    out(cP, h(<g^a(i),gb>,kP));
    in(cP, challenge);
    try find j such that gb = g^b(j) in
      out(cP, ok)
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
      out(cS, ok)
    else
      out(cS, diff(ok,ko))
  else null

system (!_i P(i) | !_j S(j)).

(* We prove several lemmas, characterizing when an action's condition passes.
   The characterization is expressed as a property of the trace that the attacker
   already has, showing that the condition does not bring him extra knowledge.

   Prove that the condition of A does not give any information to the attacker,
   by proving that it is equivalent to a trivial formula that the attacker can
   compute. It is a bit troublesome, because the formula depends on ks, which needs
   to disappear. We would not have this issue if we used a classical asymmetric
   signature scheme. *)

(* Show that condition S1 implies the next one. *)
goal S1_charac :
  forall (r:index),
      cond@S1(r) =>
        exists (s:index),  input@S(r) = g^a(s).
Proof.
(* rem -> electric-indent-mode *)

simpl.
expand cond@S1(r).
euf M0.
exists i.


Qed.

















(* Show that condition S1 implies the next one. *)
goal P1_charac :
  forall (r:index),
    cond@P1(r) =>
      exists (s:index), snd(fst(input@P1(r))) = g^b(s).
Proof.
  simpl.
  expand cond@P1(r).
  euf M0.
  exists j.
Qed.

equiv unreach.
Proof.

Qed.












































Proof.
   enrich kP; enrich kS; enrich seq(i->g^a(i));enrich seq(i->g^b(i)).

    induction t.

   expand  seq(i->g^a(i)), i.

expand  seq(i->g^a(i)), i;     expand gb(i)@P1(i).
expandall.



    fa 6.

    expand gb(i)@P2(i,j);
    expand seq(i->g^b(i)), j;
    expand seq(i,j->(diff(g^a(i)^b(j), g^k(i,j)))), i, j.

   expand frame@P3(i); expand exec@P3(i); expand output@P3(i).
   equivalent cond@P3(i), False.
   expand cond@P3(i).
   executable pred(P3(i)).

   depends P1(i), P3(i).
   use H1 with P1(i).
   use P1_charac with i.
   use H0 with s.

   expand gb(i)@P3(i). fa 5.  noif 6. simpl.

   expand gb(i)@A(i);
   expand  seq(i->g^a(i)), i.

   expandall.
   expand  seq(i->g^b(i)), j.
   fa 6.

   expand  seq(i->g^b(i)), j.

   expand  seq(i->g^a(i)), l;
   expand seq(i,j->(diff(g^a(i)^b(j), g^k(i,j)))), l, j.


   expand frame@S3(j); expand exec@S3(j).
   (* Unreachability of S3  *)
   equivalent cond@S3(j), False.
   expand cond@S3(j).
   executable pred(S3(j)).
   depends S1(j), S3(j).
   use H1 with S1(j).
   use S1_charac with j.
   use H0 with s.

   fa 5.
   noif 6. simpl.

   expand  seq(i->g^b(i)), j.

Qed.
