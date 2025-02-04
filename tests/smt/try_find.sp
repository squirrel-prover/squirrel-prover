include Core.
set smtSteps = 100000.

abstract tau:index*index->timestamp.

abstract phi : index->index->bool.

lemma[any] _ (cond:bool) : 
 if cond then try find i j such that phi i j in input@tau(i,j) else empty else empty = 
 try find i j such that cond && phi i j in input@tau(i,j) else empty.
Proof. smt. Qed.

lemma [any] _ (i0:index) :
  (try find i such that i = i0 in input@tau(i,i0)) = input@tau(i0,i0).
Proof. smt. Qed.

lemma [any] _ (i0:index) :
  (try find i j such that i = i0 && i = j in input@tau(i,j)) = input@tau(i0,i0).
Proof. smt. Qed.

(* FIXME: concrete: restore example *)
(* lemma [any] _ (i0:index) : *)
(*   (try find i j k such that i = i0 && i = j && j = k in input@tau(i,k)) = input@tau(i0,i0). *)
(* Proof. smt. Qed. *)

lemma [any] _ (i0:index) :
  (try find i j k l such that i = i0 && i = j && j = k && k = l in input@tau(i,l)) = input@tau(i0,i0).
Proof. smt ~prover:CVC5. Qed.

lemma [any] _ (i0:index) :
  (try find i j k l such that i = i0 && i = j &&  k = l in input@tau(i,l)) = input@tau(i0,i0).
Proof. checkfail (smt ~steps:10000) exn Failure. Abort.

lemma [any] _ (i0:index) :
  (try find i j such that i = i0 && i = j in input@tau(i,j)) = input@tau(i0,i0).
Proof. smt. Qed.

abstract f : index -> message.

lemma [any] _ :
  (try find i j such that f i = empty in <f i, f j>) =
  (try find i j such that f i = empty in <empty, f j>).
Proof. smt. Qed.

lemma [any] introTryFind :
  forall x:message, forall m:index -> index -> message, 
   x = try find i j such that x = m i j in m i j else x. 
Proof. smt. Qed.



abstract g : bool -> bool.
abstract h : bool. 

lemma[any] _ : (not (g true || g false) => h) => (try find x such that (g x) in (g x) else h).
 Proof. smt. Qed.

lemma[any] _ : (not (g true || g false) => h) => 
  (try find x y z such that (g x) && y && z in (g x) else h).
 Proof. smt ~prover:CVC5. Qed.



