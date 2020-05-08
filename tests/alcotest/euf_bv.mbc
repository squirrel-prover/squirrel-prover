hash h
name k : index->message
name n : index->index->message
abstract ok : message
channel c

system out(c,seq(i,j -> h(n(i,j),k(i)))).

goal forall (tau:timestamp, j,j1,j2:index),
  (if cond@tau then ok else ok) = h(n(j1,j2),k(j)) => j1=j2.
Proof.
  intros.
  euf M0.
  (* There should be two goals, for A1 and A, corresponding
   * to the two branches of the system's conditional featuring
   * relevant hashes.
   * The goals should not be provable, as was the case in previous
   * versions of the tactic where the bound variables were confused
   * with the initial goal's variables. *)
Qed. 
