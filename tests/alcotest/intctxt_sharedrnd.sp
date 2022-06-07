

(* Testing intctxt. *)

senc enc,dec
name r : message
name n : message
name m : message
name m2 : message

name k : message
channel c

abstract u : message

system (out(c,enc(m,r,k)) |   out(c,enc(m2,r,k)) | ( in(c,x); let y = dec(x,k) in out(c,y))).

goal _ : happens(A2) => output@A2 <> fail => output@A2 = m.
Proof.
  intro Hap H.
  rewrite /output /y in H.
  nosimpl(intctxt H).
Qed.
