name n : index->message

channel c

system !_i out(c,n(i)).

goal forall (j:index,t:timestamp) n(j) = input@t => A(j) < t.
Proof.
nosimpl(intro j t Heq).
nosimpl(fresh Heq; intro H).
(* TODO: destruct H and complete the proof. *)
nosimpl(substitute j,i).
nosimpl(assumption).
Qed.
