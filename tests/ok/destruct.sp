system null.

axiom exists_idx : exists (i:index), True.

lemma _ : False.
Proof.
  have [i Meq] := exists_idx.
Abort.  

lemma _ (x,y,a,b : message) : <x,y> = <a,b> => x = a && y = b.
Proof.
  intro [H1 H2]. 
  split; assumption.
Qed.

(*------------------------------------------------------------------*)
lemma _ (x, y : boolean) : (x <=> y) => x => y.
Proof. 
  intro [H1 H2].
  assumption H1.
Qed.

lemma _ (x, y : boolean) : (x <=> y) => y => x.
Proof. 
  intro [H1 H2].
  assumption H2.
Qed.

(*------------------------------------------------------------------*)
lemma _ (x, y : boolean) : (x <=> y) => y => x.
Proof.
  intro [H1 H2].
  assumption H2.
Qed.

global lemma _ (x, y : boolean) : [x <=> y] -> [x => y].
Proof. intro H1.
  localize H1 as H2. 
  destruct H2 as [H2 H3].
  assumption H2.
Qed.
