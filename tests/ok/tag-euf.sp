set processStrictAliasMode=true.

include Basic.

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

abstract g : message
abstract (^) : message -> message -> message

hash h with oracle forall (m:message,sk:message) 
 ( sk <> kP || exists (i:index) m = g ^ a(i)).

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
 happens (OutFalse) => exec@OutFalse => False.
Proof.
 intro Hap He.
 executable OutFalse; 
 1,2: auto.
 intro Hexec.
 depends Out, OutFalse; 1: auto.
 intro Hle.
 use Hexec with Out as Meq.
 rewrite /exec in Meq. 

 destruct Meq as [Hexec0 Hcond].

 expand exec@OutFalse; expand cond@Out; expand cond@OutFalse.
 destruct He as [_ [He H1]].
 euf Hcond.
 (* we prove the goal where the message satisfies the tag *)
 intro [Hneq | [i Heq]]. 
 auto.

 by use He with i.  
 auto.
 auto.
Qed.
