include Basic.

hint rewrite fst_pair.
hint rewrite snd_pair.

goal [any] _ (a,b,c : message) : a = c => fst(<a,b>) = c.
Proof. 
 intro H.
 simpl.
 assumption.
Qed.

goal [any] _ (a,b,c : message) : a = c => fst(<b,a>) = c.
Proof. 
 intro H.
 simpl.
 checkfail auto exn GoalNotClosed.
Abort.

goal [any] _ (a,b,c : message) : a = c => fst(snd(<b, <a,b>>)) = c.
Proof. 
 intro H.
 simpl.
 assumption.
Qed.

(*------------------------------------------------------------------*)
(* false axiom in general, true only if the type 'a is not empty. *)
axiom [any] exists_true1 ['a] : (exists (x : 'a), true) = true.

goal [any] _ :
 try find i : index such that (exists (j : index), i = j && i <> j)
 in zero else empty
 =
 empty.
Proof. by rewrite [/= ~constr] exists_false1 /=. Qed.

goal [any] _ :
 try find i : index such that not (exists (j : index), not (i = j && i <> j))
 in zero else empty
 =
 empty.
Proof. by rewrite [/= ~constr] exists_true1 /=. Qed.
