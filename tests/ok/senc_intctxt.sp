set autoIntro=false.

(* Testing euf over signatures. *)

senc enc,dec
name r : message
name n : message
name m : message

name k : message
channel c

abstract u : message

system (out(c,enc(m,r,k)) | ( in(c,x); let y = dec(x,k) in out(c,y))).

goal _: happens(A1) => output@A1 <> fail => output@A1 = m.
Proof.
  intro Hap Hneq.
  rewrite /output /y in Hneq.
  nosimpl(intctxt Hneq);
  by rewrite /output /y.
Qed.
