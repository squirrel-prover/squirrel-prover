(*------------------------------------------------------------------*)
(* many versions of the same lemma. *)

goal [any] mult_left_apply (a, y, z : E) : y = z => a ** y = a ** z.
Proof. auto. Qed.

(*------------------------------------------------------------------*)
(* pairs *)

goal [any] pair_eq_pair (x,y,x',y':message) :
(<x,y> = <x',y'>) = (x = x' && y = y').
Proof.
  rewrite eq_iff; split; intro H.
  split.
  by apply f_apply fst in H.
  by apply f_apply snd in H.
  auto.
Qed.

(*------------------------------------------------------------------*)
(* others *)

goal [any] le_pred_lt (t, t' : timestamp): (t <= pred(t')) = (t < t').
Proof. 
  by rewrite eq_iff.
Qed.

goal [any] le_not_lt (t, t' : timestamp): 
  t <= t' => not (t < t') => t = t'.
Proof.
  by case t' = init. 
Qed.

goal [any] le_not_lt_charac (t, t' : timestamp):
 (not (t < t') && t <= t') = (happens(t) && t = t').
Proof.
 by rewrite eq_iff.
Qed.

(* special case of [le_lt] on timestamp, can be proved. *)
goal le_lt_ts (t, t' : timestamp):
  t <> t' => (t <= t') = (t < t').
Proof.
  by intro *; rewrite eq_iff.
Qed.

axiom [any] lt_impl_le ['a] (x, x' : 'a): 
  x < x' => x <= x'.

axiom [any] le_lt ['a] (x, x' : 'a): 
  x <> x' => (x <= x') = (x < x').

(*==================================================================*)
(* Group axiomatisation *)

axiom [any] toG_ofG (x: G): toG(ofG(x)) = x.
hint rewrite toG_ofG.

goal [any] ofG_inj (x,y: G): ofG(x) = ofG(y) => x = y.
Proof. 
  intro H. 
  by apply f_apply toG in H; rewrite !toG_ofG in H. 
Qed.

goal [any] ofG_inj_eq (x,y: G): (ofG(x) = ofG(y)) = (x = y).
Proof. 
 rewrite eq_iff.
 split; 2: auto.
 by intro _; apply ofG_inj _ _.
Qed.
hint rewrite ofG_inj_eq.

axiom [any] exp_mult (x, y : E) : gen ^ x ^ y = gen ^ (x ** y).
hint rewrite exp_mult.

(* G is a prime-order group without the unit element  *)
axiom [any] gen_inj (x, y : E, z : G) : z ^ x = z ^ y => x = y.

goal [any] gen_inj_eq (x, y : E, z : G) : (z ^ x = z ^ y) = (x = y).
Proof. 
 rewrite eq_iff.
 split; 2: auto.
 by intro _; apply gen_inj _ _ z.
Qed.

(* discrete logarithm *)
axiom [any] dlog_gen : dlog (gen) = E_e.
hint rewrite dlog_gen.

axiom [any] dlog_exp (x : G, y : E): dlog (x ^ y) = dlog(x) ** y.
hint rewrite dlog_exp.

axiom [any] dlog_ax (x : G): gen ^ dlog (x) = x.

(* inv_E is the inverse function *)
axiom [any] inv_E_ax_l (x : E) : inv_E(x) ** x = E_e.
hint rewrite inv_E_ax_l.

(* ** is commutative *)
axiom [any] E_com (x, y : E) : x ** y = y ** x.

(* unit *)
axiom [any] E_e_mult_l (x : E) : x ** E_e = x.
hint rewrite E_e_mult_l.

(* ** is associative *)
axiom [any] E_assoc (x, y, z : E) : (x ** y) ** z = x ** (y ** z). 

goal [any] inv_E_ax_r (x : E) : x ** inv_E(x) = E_e.
Proof.
 by rewrite E_com; apply inv_E_ax_l.
Qed.
hint rewrite inv_E_ax_r.

goal [any] mult_inv_l (x,y,z : E) : x ** y = z => x = z ** inv_E(y).
Proof.
  by intro H; rewrite -H E_assoc inv_E_ax_r E_e_mult_l.
Qed.

goal [any] E_e_mult_r (x : E) : E_e ** x = x.
Proof.
  by rewrite E_com E_e_mult_l.
Qed.
hint rewrite E_e_mult_r.

goal [any] mult_inj (a,x,y : E) : a ** x = a ** y => x = y.
Proof.
  intro H.
  apply mult_left_apply (inv_E (a)) in H.
  by rewrite !-E_assoc !inv_E_ax_l !E_e_mult_r in H.
Qed.

goal [any] inv_inv (x : E) : inv_E(inv_E(x)) = x.
Proof.
  apply mult_inj (inv_E (x)).
  by rewrite inv_E_ax_l inv_E_ax_r.  
Qed.
hint rewrite inv_inv.

(*==================================================================*)
(* Function axioms. *)

(*------------------------------------------------------------------*)
(* option type *)

axiom [any] neq_option (x : message): (Some(x) = None) = false.
hint rewrite neq_option.

axiom [any] oget_some  (x : message): oget(Some(x)) = x.
hint rewrite oget_some.
