(* Testing euf over signatures. *)

hash h
signature sign, checksign, pk
name n : message
name m : message

name k : message
channel c

abstract u : message

system (out(c,sign(m,k)) | ( in(c,x); if checksign(x,pk(k))=n then out(c,x))).

goal forall tau:timestamp, cond@A1 => False.
Proof.
  intro tau Hcond.
  expand cond@A1.
  nosimpl(euf Hcond).
  auto.
Qed.
