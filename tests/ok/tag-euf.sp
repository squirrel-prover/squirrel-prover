set processStrictAliasMode=true.

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
  Pout: out(cP, <g^a0, h(g^a0,kP)>)

process S =
  in(cS, sP);
  if h(fst(sP),kP) = snd(sP) then
    Out : out(cS,ok);
    in(cS, challenge);
    if fst(sP)=g^a0 then
      OutIf: out(cS,okSess0)
    else
      try find l such that fst(sP) = g^a(l) in
        OutTrue: out(cS, okSessi)
      else
       OutFalse: out(cS, ko)
  else Selse: null

system (P | S).

goal charac :
  exec@OutFalse => False.
Proof.
 simpl.
 executable OutFalse.
 depends Out, OutFalse.
 apply H1 to Out.
 expand exec@Out.
 nosimpl(expand exec@OutFalse; expand cond@Out;  expand cond@OutFalse; simpl).
 euf M0.
 (* we prove the goal where the message satisfies the tag *)
 case H5.
 apply H2 to i.
 nosimpl(notleft H3).
 (* the honnestly produced hash case is direclty in contradiciton with the condition of S *)
 simpl.
Qed.
