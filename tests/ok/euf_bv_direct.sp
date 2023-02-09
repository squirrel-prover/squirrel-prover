

(* Testing euf's behaviour when bound variables are used in direct cases. *)

hash h
name k : index * index -> message
name n : index * index -> message

system null.

(* Here, there should be single direct case in euf tactic,
 * where the same variable v is introduced to represent the bound
 * index a. Then n(v,v) = n(i,j) and thus i=j. *)
goal _ (i,j,w:index[param]):
  seq(a,b:index => h(n(a,a),k(b,b))) = h(n(i,j),k(w,w)) =>
  i = j.
Proof.
  intro Hseq.
  euf Hseq.
  auto.
Qed.

(* Similar to previous example but this time the equality i=j
 * comes from the index constraints on key indices. *)
goal _ (i,j,w:index[param]):
  seq(a,b:index => h(n(a,a),k(b,b))) = h(n(w,w),k(i,j)) =>
  i = j.
Proof.
  intro Hseq.
  euf Hseq.
  auto.
Qed.
