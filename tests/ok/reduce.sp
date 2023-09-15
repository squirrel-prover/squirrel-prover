include Basic.

hint rewrite fst_pair.
hint rewrite snd_pair.

lemma [any] _ (a,b,c : message) : a = c => fst(<a,b>) = c.
Proof. 
 intro H.
 simpl.
 assumption.
Qed.

lemma [any] _ (a,b,c : message) : a = c => fst(<b,a>) = c.
Proof. 
 intro H.
 simpl.
 checkfail auto exn GoalNotClosed.
Abort.

lemma [any] _ (a,b,c : message) : a = c => fst(snd(<b, <a,b>>)) = c.
Proof. 
 intro H.
 simpl.
 assumption.
Qed.

(*------------------------------------------------------------------*)
(* false axiom in general, true only if the type 'a is not empty. *)
axiom [any] exists_true1 ['a] : (exists (x : 'a), true) = true.

lemma [any] _ :
 try find i such that (exists (j : index), i = j && i <> j)
 in zero else empty
 =
 empty.
Proof. by rewrite [/= ~constr] exists_false1 /=. Qed.

lemma [any] _ :
 try find i such that not (exists (j : index), not (i = j && i <> j))
 in zero else empty
 =
 empty.
Proof. by rewrite [/= ~constr] exists_true1 /=. Qed.

(*==================================================================*)
(* small tests for flags and rewriting *)

axiom [any] foo (x,y : message): (x,y)#1 = y.

lemma [any] _ (a,b : message) : (a,b)#1 = b.
Proof. 
  checkfail rewrite /= foo exn Failure.
  checkfail rewrite [/= ~flags:[proj]] foo exn Failure.
  rewrite [/= ~flags:[]]. 
  rewrite foo. 
  apply eq_refl.
Qed.

lemma [any] _ (a,b : message) : (a,b)#1 = b.
Proof. 
  checkfail simpl; rewrite foo exn Failure.
  checkfail simpl ~flags:[proj]; rewrite foo exn Failure.
  simpl ~flags:[].
  rewrite foo. 
  apply eq_refl.
Qed.

lemma [any] _ (a,b : message) : (a,b)#1 = b.
Proof. 
  checkfail reduce; rewrite foo exn Failure.
  checkfail reduce ~flags:[proj]; rewrite foo exn Failure.
  reduce ~flags:[].
  rewrite foo. 
  apply eq_refl.
Qed.

(*------------------------------------------------------------------*)
axiom [any] bar (a,b : message) : (fun x y => y) a b = a.

lemma [any] _ (a,b : message) : 
  (fun x y => y) a b = a.
Proof. 
  checkfail rewrite /= bar exn Failure.
  checkfail rewrite [/= ~flags:[beta]] bar exn Failure.
  rewrite [/= ~flags:[]]. 
  rewrite bar. 
  apply eq_refl.
Qed.

lemma [any] _ (a,b : message) : 
  (fun x y => y) a b = a.
Proof. 
  checkfail simpl; rewrite bar exn Failure.
  checkfail simpl ~flags:[beta]; rewrite bar exn Failure.
  simpl ~flags:[]. 
  rewrite bar. 
  apply eq_refl.
Qed.

lemma [any] _ (a,b : message) : 
  (fun x y => y) a b = a.
Proof. 
  checkfail reduce; rewrite bar exn Failure.
  checkfail reduce ~flags:[beta]; rewrite bar exn Failure.
  reduce ~flags:[]. 
  rewrite bar. 
  apply eq_refl.
Qed.


