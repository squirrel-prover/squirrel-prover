set autoIntro=false.

(* Testing intctxt. *)

senc enc,dec
name r : message
name n : message
name m : message

name k : message
channel c

abstract u : message

system (out(c,enc(m,r,k)) | out(c,r) |  ( in(c,x); let y = dec(x,k) in out(c,y))).

goal output@A2 <> fail => output@A2 = m.
Proof.
  intro Hneq.
  nosimpl(intctxt D).

  simpl.
  simpl.
Qed.
