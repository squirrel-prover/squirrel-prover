

(* Testing intctxt. *)

senc enc,dec
name r : message
name n : message
name m : message

name k : message
channel c

abstract u : message

system (out(c,enc(m,r,k)) | out(c,r) |  ( in(c,x); let y = dec(x,k) in out(c,y))).

goal _ : happens(A2) => output@A2 <> fail => output@A2 = m.
Proof.
  intro Hap Hneq.
  rewrite /output /y in Hneq.
  nosimpl(intctxt Hneq).
Qed.
