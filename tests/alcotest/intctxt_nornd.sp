

(* Testing intctxt. *)

senc enc,dec
name r : message
name n : message
name m : message

name k : message
channel c

abstract u : message

system (out(c,enc(m,u,k)) | ( in(c,x); let y = dec(x,k) in out(c,y))).

goal _ : happens(A1) => output@A1 <> fail => output@A1 = m.
Proof.  
  intro Hap H.
  rewrite /output /y in H.
  nosimpl(intctxt H).
Qed.
