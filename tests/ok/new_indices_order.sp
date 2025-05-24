(* When a variable bound by "new" is replaced by a name,
   check that indices are applied in the right order. *)

channel c.

system !_i !_j new n; out(c,n).

lemma _ : forall i j, happens(A(i,j)) => output@A(i,j) = n(i,j).
Proof.
  intro i j H.
  (* Check that namelength_n takes argument in proper order. *)
  assert len(n(i,j)) = namelength_message by apply namelength_n (i,j).
  rewrite /output.
  auto.
Qed.

(* In the next system, m should be indexed by index*bool:
   the order matters also for types. *)

system Test = !_i try find b such that true in new m; out(c,m).

lemma [Test] _ : forall i b, happens(A1(i,b)) => output@A1(i,b) = m(i,b).
Proof.
  intro i b H.
  (* Check that namelength_m takes argument in proper order. *)
  assert len(m(i,b)) = namelength_message by apply namelength_m (i,b).
  rewrite /output.
  auto.
Qed.
