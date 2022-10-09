

(* Testing euf over signatures. *)

hash h
signature sign, checksign, pk
name n : message
name m : message

name k : message
channel c

abstract u : message

system (out(c,sign(m,k)) | ( in(c,x); if checksign(n,x,pk(k)) then out(c,x))).

goal _ (tau:timestamp): happens(A1) => cond@A1 => False.
Proof.
  intro Hap Hcond.
  expand cond@A1.
  nosimpl(euf Hcond).
  auto.
Qed.
