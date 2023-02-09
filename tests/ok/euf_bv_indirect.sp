(* Testing euf's behaviour when bound variables are used in indirect cases. *)

hash h
name k : index * index -> message
name n : index * index -> message

channel c

system out(c,seq(a,b:index => h(n(a,a),k(b,b)))).

(* Here, there should be single direct case in euf tactic,
 * where the same variable v is introduced to represent the bound
 * index a. Then n(v,v) = n(i,j) and thus i=j. *)
goal _ (tau:timestamp[param],i,j,w:index[param]):
  happens(tau) => output@tau = h(n(i,j),k(w,w)) =>
  i = j.
Proof.
  intro Hap Heq.
  euf Heq.
  auto.
Qed.

(* Similar to previous example but this time the equality i=j
 * comes from the index constraints on key indices. *)
goal _ (tau:timestamp[param],i,j,w:index[param]):
  happens(tau) => output@tau = h(n(w,w),k(i,j)) =>
  i = j.
Proof.
  intro Hap Heq.
  euf Heq.
  auto.
Qed.
