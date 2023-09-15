(* test that `rewrite` cannot do too much when rewritting under a
   binder *)

include Basic.

system null.

name m : index -> message.

(* `index` is finite+fixed, hence it is almost always 
   true that `forall i, m i <> t`.  *)
global lemma Gi (t : _[const]) : [forall i, m i <> t].
Proof. 
  intro i => Meq. 
  fresh Meq. 
Qed.

op ptrue ['a] = fun x : 'a => true.

lemma _ (t : _[const,glob]) : (fun i => m i <> t) = ptrue.
Proof.
  rewrite Gi. 
  rewrite /ptrue //.
Qed.

(* ------------------------------------------------------------------- *)

(* finite but not fixed *)
type I[finite].

name n : I -> message.

(* It is not true that `forall i, n i <> t` is almost always true,
   because `I` is a finite but possibly large type (hence there 
   is a high probability of having a collision between one of 
   the `n i` and `t`) *)
global lemma _ (t : _[const]) : [forall i, n i <> t].
Proof. 
  intro i => Meq. 
  checkfail fresh Meq exn Failure.
Abort.

(* adding `const` allows to conclude *)
global lemma GI (t : _[const]) : Forall (i : _[const]), [n i <> t].
Proof.  
  intro i => Meq. 
  fresh Meq.
Qed.

(* it is not true that `fun i => n i <> t` is almost always true,
because `I` is a finite but possibly large type (hence there is a high
probability of having a collision between one of the `n i` and `t`*)
lemma _ (t : _[const,glob]) : (fun i => n i <> t) = ptrue.
Proof.
  checkfail rewrite GI exn Failure. (* bad variable instantiation *)
Abort.
