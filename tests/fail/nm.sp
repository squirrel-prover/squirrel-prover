set autoIntro=false.

channel c

aenc enc,dec,pk
name r : message
name n : message
name m : message

name k : message

abstract u : message



system  [sharedrnd] (I : out(c,enc(n,r,pk(k))) | out(c,enc(m,r,pk(k))) | ( in(c,x); if dec(x,k)=n then R : out(c,x))).

goal  [sharedrnd] _: happens(R) => cond@R => input@R = output@I.
Proof.
  intro Hap Hcond.
  rewrite /cond in Hcond.
  checkfail nm Hcond exn SEncSharedRandom.
Abort.


system  [nornd] (I: out(c,enc(n,u,pk(k))) | ( in(c,x); if dec(x,k)=n then A : out(c,x))).

goal  [nornd] _: happens(A) => cond@A => input@A = output@I.
Proof.
  intro Hap Hcond.
  rewrite /cond in Hcond.
  checkfail nm Hcond exn SEncNoRandom.
Abort.


system  [nothiddenname] (I : out(c,<enc(n,r,pk(k)),n>) | ( in(c,x); if dec(x,k)=n then A : out(c,x))).

goal  [nothiddenname] _: happens(A) => cond@A => input@A = output@I.
Proof.
  intro Hap Hcond.
  rewrite /cond in Hcond.
  checkfail nm Hcond exn NameNotUnderEnc.
Abort.

system [nothiddennamepaired] (I : out(c,<enc(<n,m>,r,pk(k)), n>) | ( in(c,x); if dec(x,k)=<n,m> then A : out(c,x))).

goal [nothiddennamepaired]  _: happens(A) => cond@A => input@A = fst(output@I).
Proof.
  intro Hap Hcond.
  rewrite /cond in Hcond.
  checkfail (nm Hcond, n) exn NameNotUnderEnc.
  nosimpl(nm Hcond, m).
  by simpl.
  by simpl.
Qed.
