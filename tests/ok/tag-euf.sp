abstract okSess0 : message
abstract okSessi : message
abstract ko : message
abstract ok : message

name kP : message
name kS : message

channel cP
channel cS

name a0 :message
name a : index -> message

hash h with oracle forall (m:message,sk:message) ( sk <> kP || exists (i:index) m=g^a(i))

term test : boolean = zero

process P =
  out(cP, <g^a0, h(g^a0,kP)>)

process S =
  in(cS, sP);
  if h(fst(sP),kP) = snd(sP) then
    out(cS,ok);
    in(cS, challenge);
    if fst(sP)=g^a0 then
      out(cS,okSess0)
    else
      try find l such that fst(sP) = g^a(l) in
        out(cS, okSessi)
      else
        out(cS, ko)
  else null

system (P | S).

goal S1_charac :
  exec@S3 => False.
Proof.
 simpl.
 executable S3.
 depends S, S3.
 apply H1 to S.
 expand exec@S.
 nosimpl(expand exec@S3; expand cond@S;  expand cond@S3; simpl).
 euf M0.
 (* we prove the goal where the message satisfies the tag *)
 case H5.
 apply H2 to i.
 nosimpl(notleft H3).
 (* the honnestly produced hash case is direclty in contradiciton with the condition of S *)
 simpl.
Qed.