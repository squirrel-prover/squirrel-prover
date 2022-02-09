set autoIntro=false.

(* (* comment out to work on the librairie *) *)
(* system null. *)

(*------------------------------------------------------------------*)
(* equality *)

axiom eq_iff (x, y : boolean) : (x = y) = (x <=> y).

goal eq_sym ['a] (x,y : 'a) : (x = y) = (y = x).
Proof. by rewrite eq_iff. Qed.

goal eq_refl ['a] (x : 'a) : (x = x) = true. 
Proof. 
  by rewrite eq_iff. 
Qed.
hint rewrite eq_refl.

(*------------------------------------------------------------------*)
(* true/false *)

axiom true_false : (true = false) = false.
hint rewrite true_false.

goal false_true : (false = true) = false.
Proof. 
  by rewrite (eq_sym false true).
Qed.
hint rewrite false_true.

(*------------------------------------------------------------------*)
(* not *)

axiom not_true : not(true) = false.
hint rewrite not_true.

axiom not_false : not(false) = true.
hint rewrite not_false.


goal not_not (b : boolean): not (not b) = b. 
Proof.
  by case b.
Qed.
hint rewrite not_not.

goal not_eq ['a] (x, y : 'a): not (x = y) = (x <> y).
Proof. 
by rewrite eq_iff. 
Qed.
hint rewrite not_eq.

goal not_neq ['a] (x, y : 'a): not (x <> y) = (x = y).
Proof. 
by rewrite eq_iff. 
Qed.
hint rewrite not_neq.

(*------------------------------------------------------------------*)
(* disequality *)

goal eq_false ['a] (x, y : 'a): ((x = y) = false) = (x <> y).
Proof. 
rewrite -not_eq. case (x = y) => _. simpl. auto.
by rewrite eq_iff. 
Qed.
hint rewrite eq_false.

(*------------------------------------------------------------------*)
(* and *)

axiom and_comm (b,b' : boolean) : (b && b') = (b' && b).

axiom and_true_l (b : boolean) : (true && b) = b.
hint rewrite and_true_l.

goal and_true_r (b : boolean) : (b && true) = b.
Proof. by rewrite and_comm and_true_l. Qed.
hint rewrite and_true_r.

axiom and_false_l (b : boolean) : (false && b) = false.
hint rewrite and_false_l.

goal and_false_r (b : boolean) : (b && false) = false.
Proof. by rewrite and_comm and_false_l. Qed.
hint rewrite and_false_r.

(*------------------------------------------------------------------*)
(* or *)
axiom or_comm (b,b' : boolean) : (b || b') = (b' || b).

axiom or_false_l (b : boolean) : (false || b) = b.
hint rewrite or_false_l.

goal or_false_r (b : boolean) : (b || false) = b.
Proof. by rewrite or_comm or_false_l. Qed.
hint rewrite or_false_r.

axiom or_true_l (b : boolean) : (true || b) = true.
hint rewrite or_true_l.

goal or_true_r (b : boolean) : (b || true) = true.
Proof. by rewrite or_comm or_true_l. Qed.
hint rewrite or_true_r.


(*------------------------------------------------------------------*)
(* not: more lemmas *)

goal not_and (a, b : boolean): not (a && b) = (not a || not b).
Proof. 
  rewrite eq_iff. 
  case a; case b => //=.
Qed.

goal not_or (a, b : boolean): not (a || b) = (not a && not b).
Proof. 
  rewrite eq_iff. 
  case a; case b => //=.
Qed.

(*------------------------------------------------------------------*)
(* if *)

goal if_true ['a] (b : boolean, x,y : 'a):
 b => if b then x else y = x.
Proof.
  by intro *; yesif.
Qed.

goal if_true0 ['a] (x,y : 'a):
 if true then x else y = x.
Proof.
  by rewrite if_true. 
Qed.
hint rewrite if_true0.

goal if_false ['a] (b : boolean, x,y : 'a):
 (not b) => if b then x else y = y.
Proof.
  by intro *; noif.
Qed.

goal if_false0 ['a] (x,y : 'a):
 if false then x else y = y.
Proof.
  by rewrite if_false.
Qed.
hint rewrite if_false0.

goal if_then_then ['a] (b,b' : boolean, x,y : 'a):
  if b then (if b' then x else y) else y = if (b && b') then x else y.
Proof.  
  by case b; case b'.
Qed.

goal if_same ['a] (b : boolean, x : 'a):
  if b then x else x = x.
Proof.
  by case b.
Qed.
hint rewrite if_same.

goal if_then ['a] (b,b' : boolean, x,y,z : 'a):
 b = b' => 
 if b then (if b' then x else y) else z = 
 if b then x else z.
Proof.
  by intro ->; case b'.
Qed.
hint rewrite if_then.

goal if_else ['a] (b,b' : boolean, x,y,z : 'a):
 b = b' => 
 if b then x else (if b' then y else z) = 
 if b then x else z.
Proof.
  by intro ->; case b'.
Qed.
hint rewrite if_else.

goal if_then_not ['a] (b,b' : boolean, x,y,z : 'a):
 b = not b' => 
 if b then (if b' then x else y) else z = 
 if b then y else z.
Proof.
  by intro ->; case b'.
Qed.
hint rewrite if_then_not.

goal if_else_not ['a] (b,b' : boolean, x,y,z : 'a):
  b = not b' => 
 if b then x else (if b' then y else z) = 
 if b then x else y.
Proof.  
  by intro ->; case b'.
Qed.
hint rewrite if_else_not.

(*------------------------------------------------------------------*)
(* some functional properties *)

goal fst_pair (x,y : message) : fst (<x,y>) = x.
Proof. auto. Qed.
hint rewrite fst_pair.

goal snd_pair (x,y : message) : snd (<x,y>) = y.
Proof. auto. Qed.
hint rewrite snd_pair.

(*------------------------------------------------------------------*)
(* diff *)

goal diff_eq ['a] (x,y : 'a) : x = y => diff(x,y) = x.
Proof. by project. Qed.
hint rewrite diff_eq.

goal diff_diff_l ['a] (x,y,z: 'a): diff(diff(x,y),z) = diff(x,z).
Proof. by project. Qed.
hint rewrite diff_diff_l.

goal diff_diff_r ['a] (x,y,z: 'a): diff(x,diff(y,z)) = diff(x,z).
Proof. by project. Qed.
hint rewrite diff_diff_r.

goal len_diff (x, y : message) : len(diff(x,y)) = diff(len(x), len(y)).
Proof. by project. Qed.


(*------------------------------------------------------------------*)
(* if-and-only-if *)

goal iff_refl (x : boolean) : (x <=> x) = true.
Proof.
 by rewrite eq_iff. 
Qed.
hint rewrite iff_refl.

goal iff_sym (x, y: boolean) : (x <=> y) = (y <=> x). 
Proof.
 by rewrite eq_iff. 
Qed.

goal true_iff_false : (true <=> false) = false.
Proof.
 by rewrite -eq_iff. 
Qed.
hint rewrite true_iff_false.

goal false_iff_true : (false <=> true) = false.
Proof.
 by rewrite -eq_iff. 
Qed.
hint rewrite false_iff_true.
