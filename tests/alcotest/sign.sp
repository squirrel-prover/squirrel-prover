(* Testing that the presence of hash with some key, renders invalid euf for a
signature. *)

hash h
signature sign, checksign, pk
name n : message
name m : message

name k : message
channel c

abstract u : message

system (out(c,h(m,k)) | ( in(c,x); if checksign(x,pk(k))=n then out(c,x))).

goal forall tau:timestamp, cond@A1 => False.
Proof.
  intros.
  expand cond@A1.
  nosimpl(euf M0).
  simpl.
Qed.
