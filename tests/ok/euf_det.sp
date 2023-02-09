channel c
hash h
name n : message
name k : index * index -> message

system !_i out(c,h(n,k(i,i))).

(*==================================================================*)
(* various sanity checks on parameters *)

(*------------------------------------------------------------------*)
(* fails if [tau] is not deterministic *)
goal _ (tau:timestamp, x : message, a,b:index[const]):
  happens(tau) => <x,output@tau> = h(n,k(a,b)) =>
  a = b.
Proof.
  intro Hap Heq.
  checkfail euf Heq exn Failure.
  (* Failure: terms contain a non-ptime variable: x *)
Abort.

(*------------------------------------------------------------------*)
(* fails if [a] or [b] is not a parameter *)
goal _ (tau:timestamp, x : message, a:index[const], b:index):
  happens(tau) => <x,output@tau> = h(n,k(a,b)) =>
  a = b.
Proof.
  intro Hap Heq.
  checkfail euf Heq exn Failure.
  (* Failure: terms contain a non-ptime variable: b *)
Abort.

goal _ (tau:timestamp, x : message, a:index, b:index[const]):
  happens(tau) => <x,output@tau> = h(n,k(a,b)) =>
  a = b.
Proof.
  intro Hap Heq.
  checkfail euf Heq exn Failure.
  (* Failure: terms contain a non-ptime variable: a *)
Abort.

goal _ (tau:timestamp, x : message, a,b:index):
  happens(tau) => <x,output@tau> = h(n,k(a,b)) =>
  a = b.
Proof.
  intro Hap Heq.
  checkfail euf Heq exn Failure.
  (* Failure: terms contain a non-ptime variable: a,b *)
Abort.
