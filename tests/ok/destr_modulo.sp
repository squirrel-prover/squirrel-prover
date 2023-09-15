include Basic.

(* ------------------------------------------------------------------- *)
(* forall *)

(* operator with a top-most forall binder *)
op ( *> ) ['a 'b] (u : 'a, m : 'b) = forall (f : 'a -> 'b), f u <> m.

lemma [any] _ ['a 'b 'c] (u : 'a, v : 'b, g : 'b -> 'c) : 
  u *> (g v).
Proof.
  intro f Eq.
Abort.

(* ------------------------------------------------------------------- *)
(* equality *)

lemma [any] _ ['a] (x1,x2,y1,y2 : 'a) :
  (x1,x2) = (y1,y2) => x1 = y1 && x2 = y2.
Proof.
  intro [Eq1 Eq2].
  split.
  + assumption Eq1.
  + assumption Eq2.
Qed.

(* operator reducing to equality *)
op ( ~~ ) ['a] (x,y:'a) = x = y.
lemma [any] _ ['a] (x1,x2,y1,y2 : 'a) :
  (x1,x2) ~~ (y1,y2) => x1 = y1 && x2 = y2.
Proof.
  intro [Eq1 Eq2].
  split.
  + assumption Eq1.
  + assumption Eq2.
Qed.


(* ------------------------------------------------------------------- *)
(* impl *)

op ( ~- ) (x,y:bool) = x => y.

lemma [any] _ (a,b : bool) :
  (a ~- a).
Proof.
  intro H.
  assumption H.
Qed.

(* ------------------------------------------------------------------- *)
(* and *)

op ( ~& ) (x,y:bool) = x && y.

lemma [any] _ (a,b : bool) :
  (a ~& b) => a && b.
Proof.
  intro [Eq1 Eq2].
  split.
  + assumption Eq1.
  + assumption Eq2.
Qed.

(* ------------------------------------------------------------------- *)
(* or *)

op ( ~| ) (x,y:bool) = x || y.

lemma [any] _ (a,b : bool) :
  (a ~| b) => a || b.
Proof.
  intro [Eq1 | Eq2].
  + left; assumption Eq1.
  + right; assumption Eq2.
Qed.
