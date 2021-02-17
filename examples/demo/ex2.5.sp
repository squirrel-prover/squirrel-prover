hash h

abstract ok : message
abstract ko : message

name kP : message
name kS : message

channel cP
channel cS

name a : index -> message

process P(i:index) =
  P : out(cP, <a(i),h(a(i),kP)>)

process S(i:index) =
  in(cS, ha);
  if snd(ha) = h(fst(ha),kP) then
    S : out(cS,ok);
    in(cS, challenge);
    (try find l such that fst(ha) = a(l) in
      S1 : out(cS, ok)
    else
      S2 : out(cS, diff(ok,ko)))
  else S3 : out(cS,ko)

system (!_i P(i) | !_j S(j)).

goal S_charac :
  forall (r:index),
      cond@S(r) =>
        exists (s:index),  fst(input@S(r)) = a(s).
Proof.
(* rem -> electric-indent-mode *)

     Qed.









simpl.
expand cond@S(r).
euf M0.
exists i.
Qed.

equiv unreach.
     Proof.















































   enrich seq(i-> a(i)). enrich kP.
   induction t.

   expandall.
   expand seq(i->a(i)),i .

   expand seq(i->a(i)),l .

   expand frame@S2(j).

     equivalent  exec@S2(j),False.
    simpl.

     expand exec@S2(j).
    use S_charac with j.
     expand cond@S2(j).

    use H0 with s.


     depends S(j), S2(j).

     executable S2(j).

     use H2 with S(j).

     fa 2.
     noif 3.
     simpl.
     Qed.
