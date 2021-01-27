(* Testing intctxt. *)

senc enc,dec
name r : message
name n : message
name m : index -> message

name k : message
channel c

abstract u : message

system ( !_i out(c,enc(m(i),r,k)) | ( in(c,x); let y = dec(x,k) in out(c,y))).

goal output@A1 <> fail => exists i:index, output@A1 = m(i).
Proof.
  simpl.
  nosimpl(intctxt D).

  simpl.
  simpl.
Qed.
