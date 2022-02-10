set autoIntro=false.

(* Testing nm over encryptions. *)

aenc enc,dec,pk
name r : message
name n : message
name m : message

name k : message
channel c

abstract u : message

system (I : out(c,enc(n,r,pk(k))) | ( in(c,x); if dec(x,k)=n then R : out(c,x))).

goal _: happens(R) => cond@R => input@R = output@I.
Proof.
  intro Hap Hcond.
  rewrite /cond in Hcond.
  nosimpl(nm Hcond).
  by simpl.
Qed.

system [paired] (I : out(c,enc(<n,m>,r,pk(k))) | ( in(c,x); if dec(x,k)=<n,m> then R : out(c,x))).

goal [paired]  _: happens(R) => cond@R => input@R = output@I.
Proof.
  intro Hap Hcond.
  rewrite /cond in Hcond.
  nosimpl(nm Hcond, n).
  by simpl.
  by simpl.
Qed.
