include Core.

type E[large, serializable].
type G[serializable].

gdh g, (^), ( ** ) where group:G exponents:E.

abstract E_e : E.
abstract inv_E : E -> E
abstract dlog : G -> E
abstract ofG : G -> message.
abstract toG : message -> G.


abstract Some : message -> message.
abstract None : message.
abstract oget : message -> message.

(*------------------------------------------------------------------*)
(* many versions of the same lemma. *)

exact lemma [any] mult_left_apply (a, y, z : E) : y = z => a ** y = a ** z.
Proof. auto. Qed.

(*------------------------------------------------------------------*)
(* pairs *)

exact lemma [any] pair_eq_pair (x,y,x',y':message) :
(<x,y> = <x',y'>) = (x = x' && y = y').
Proof.
  rewrite eq_iff; split; intro H.
  split.
  by apply f_apply fst in H.
  by apply f_apply snd in H.
  auto.
Qed.

(*==================================================================*)
(* Group axiomatisation *)

exact axiom [any] toG_ofG (x: G): toG(ofG(x)) = x.
hint rewrite toG_ofG.

exact lemma [any] ofG_inj (x,y: G): ofG(x) = ofG(y) => x = y.
Proof. 
  intro H. 
  by apply f_apply toG in H; rewrite !toG_ofG in H. 
Qed.

exact lemma [any] ofG_inj_eq (x,y: G): (ofG(x) = ofG(y)) = (x = y).
Proof. 
 rewrite eq_iff.
 split; 2: auto.
 by intro _; apply ofG_inj _ _.
Qed.
hint rewrite ofG_inj_eq.

exact axiom [any] exp_mult (x, y : E) : g ^ x ^ y = g ^ (x ** y).
hint rewrite exp_mult.

(* G is a prime-order group without the unit element  *)
exact axiom [any] g_inj (x, y : E, z : G) : z ^ x = z ^ y => x = y.

exact lemma [any] g_inj_eq (x, y : E, z : G) : (z ^ x = z ^ y) = (x = y).
Proof. 
 rewrite eq_iff.
 split; 2: auto.
 by intro _; apply g_inj _ _ z.
Qed.

(* discrete logarithm *)
exact axiom [any] dlog_g : dlog (g) = E_e.
hint rewrite dlog_g.

exact axiom [any] dlog_exp (x : G, y : E): dlog (x ^ y) = dlog(x) ** y.
hint rewrite dlog_exp.

exact axiom [any] dlog_ax (x : G): g ^ dlog (x) = x.

(* inv_E is the inverse function *)
exact axiom [any] inv_E_ax_l (x : E) : inv_E(x) ** x = E_e.
hint rewrite inv_E_ax_l.

(* ** is commutative *)
exact axiom [any] E_com (x, y : E) : x ** y = y ** x.

(* unit *)
exact axiom [any] E_e_mult_l (x : E) : x ** E_e = x.
hint rewrite E_e_mult_l.

(* ** is associative *)
exact axiom [any] E_assoc (x, y, z : E) : (x ** y) ** z = x ** (y ** z). 

exact lemma [any] inv_E_ax_r (x : E) : x ** inv_E(x) = E_e.
Proof.
 by rewrite E_com; apply inv_E_ax_l.
Qed.
hint rewrite inv_E_ax_r.

exact lemma [any] mult_inv_l (x,y,z : E) : x ** y = z => x = z ** inv_E(y).
Proof.
  by intro H; rewrite -H E_assoc inv_E_ax_r E_e_mult_l.
Qed.

exact lemma [any] E_e_mult_r (x : E) : E_e ** x = x.
Proof.
  by rewrite E_com E_e_mult_l.
Qed.
hint rewrite E_e_mult_r.

exact lemma [any] mult_inj (a,x,y : E) : a ** x = a ** y => x = y.
Proof.
  intro H.
  apply mult_left_apply (inv_E (a)) in H.
  by rewrite !-E_assoc !inv_E_ax_l !E_e_mult_r in H.
Qed.

exact lemma [any] inv_inv (x : E) : inv_E(inv_E(x)) = x.
Proof.
  apply mult_inj (inv_E (x)).
  by rewrite inv_E_ax_l inv_E_ax_r.  
Qed.
hint rewrite inv_inv.


exact lemma [any] inv_exp (u,v:G, z:E) : u^z = v^z => u=v.
Proof.
  intro E.
  apply (f_apply dlog) in E.
  rewrite !dlog_exp in E.
  rewrite E_com (E_com (dlog v) z)  in E.
  apply mult_inj in E.
  apply (f_apply (fun x => g^x)) in E. 
  simpl.
  by rewrite !dlog_ax in E. 
Qed.

(*==================================================================*)
(* Function axioms. *)

(*------------------------------------------------------------------*)
(* option type *)

exact axiom [any] neq_option (x : message): (Some(x) = None) = false.
hint rewrite neq_option.

exact axiom [any] oget_some  (x : message): oget(Some(x)) = x.
hint rewrite oget_some.


