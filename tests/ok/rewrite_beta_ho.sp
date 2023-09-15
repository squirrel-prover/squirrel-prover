(* test rewriting modulo β with higher-order matching *)

include Basic.

system [real] null.

name skR : index -> message.

lemma [real] rw (y:index) : forall x, x = y => skR x = skR y. Proof. auto. Qed.

(* manual proof, instantiating the lemma by hand *)
lemma [real] _ (j:index) :
  (try find i:index such that i = j in skR i) = (skR j).
Proof.
  rewrite (rw j) //. 
  have H := try_choose (fun i => i = j) (fun _ => skR j) zero j _; 1: auto. 
  by auto.
Qed.

(* higher-order matching + beta-reduction *)
lemma [real] _ (j:index) :
  (try find i:index such that i = j in skR i) = (skR j).
Proof.
  rewrite (rw j) // (try_choose _ (fun _ => skR j) _ j) //.
Qed.
