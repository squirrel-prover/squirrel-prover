set smtSteps=10000.

lemma [any] implies_exists2 ['a] (phi:bool,psi:'a->bool) :
  (phi => exists j:'a, psi(j)) =
  (exists x:'a, phi => psi(x)).
Proof. smt. Qed.

lemma [any] extensionnality ['a 'b] (f, g : 'a -> 'b) : 
  (forall x, f x = g x) => f = g.
Proof. smt. Qed.

lemma [any] if_application ['a 'b] (f:'a->'b) (c:bool) (x,y:'a) :
  f (if c then x else y) = if c then f x else f y.
Proof. smt. Qed.

include Logic.

lemma [any] forall_exists2 ['a 'b] (phi:'a->'b->bool) :
  (forall x:'a, exists y:'b, phi x y) =
  (exists y':'a->'b, forall x:'a, phi x (y' x)).
Proof. 
  rewrite eq_iff; split.
  + intro H. 
    exists (fun x => choose (fun y => phi x y)). (* ce choix intelligent semble nécessaire pour guider les solveurs *)
    smt ~prover:Z3. (* Ne fonctionne pas avec CVC5 qui requiert d'aller jusqu'au assert de la preuve sans smt, mais fonctionne avec l'option --enum-inst du graphe ou avec Z3. *)
  + smt.
Qed.

lemma [any] choosespec ['a] (phi:'a->bool) (x:'a) :
  phi x =>
  phi (choose phi).
Proof.
  smt.
Qed.

lemma [any] trychoose ['a 'b] (phi:'a->bool) (f:'a->'b) (g:'b) (x:'a) :
  phi x =>
  (try find x such that phi x in f x else g) =
  (f (choose phi)).
Proof.
  smt.
Qed.

lemma [any] try_carac ['a 'b] (phi:'a->bool) (f:'a->'b) (g:'b) :
  (try find x such that phi x in f x else g) =
  (if exists x, phi x then f (choose phi) else g).
Proof.
  smt.
Qed.
