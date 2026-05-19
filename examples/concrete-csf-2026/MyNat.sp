include Int.

(*induction definition of natural numbers*)
inductive nat =
| zn : nat
| sn : nat -> nat.

(*Classical order on natural number*)
let rec ltn ((x,y) : nat*nat) with
|(zn,zn) -> false
|(zn,sn(_)) -> true
|(sn(_),zn) -> false
|(sn(x),sn(y)) -> ltn (x,y).
Proof.
intro > <-; discriminate.
Qed.

(* ------------------------------------------------------------------- *)
(* conversion function to `int` and `real` and classical function on naturals *)
let rec to_int (n : nat) with
| zn -> 0
| sn(x) -> Int.(+) (to_int x) 1.
Proof.
intro > <-; discriminate.
Qed.

let rec addn (n : nat) (m : nat) with
| zn -> n
| sn(m) -> addn (sn n) m.
Proof.
intro > <-; discriminate.
Qed.

let predn (n : nat) with
| zn -> zn
| sn(x) -> x.

include Real.
namespace Real.
  let rec of_nat (n : nat) with
  | zn   -> Real.z
  | sn n -> of_int 1 + of_nat n.
  Proof. intro > <-. discriminate. Qed.
end Real.
open Real.                      (* export of_nat in the root namespace *)


(* ------------------------------------------------------------------- *)
(* basic lemmas *)
exact lemma [any] ltn_0 x : ltn (x,zn) => x = zn.
Proof.
case x; auto.
Qed.

exact lemma [any] ltn_sn x : ltn(x,sn x).
Proof.
induction x; auto.
Qed.

exact lemma [any] ltn_n_sn x y : ltn(x,y) => ltn(x,sn y).
Proof.
generalize x.
induction y.
+  intro x; case x ; auto.
+ intro y IH x; case x; [ 1,3: auto | 2 : by intro z @/ltn; apply IH].
Qed.

exact lemma [any] ltn_sn_case x y : ltn(x, sn y) => ltn(x, y) || x = y.
Proof.
generalize x.
induction y.
+ intro x; case x; [1,3 :auto | 2 :  intro y @/ltn; case y; auto].
+ intro y IH x; case x; [1,3 : auto | 2 : intro z @/ltn H1; by have [H2 | H2] := IH _ H1].
Qed.

exact lemma [any] ltn_trans x y z : ltn(x,y) && ltn(y,z) => ltn(x,z).
Proof.
generalize x y.
induction z.
+ by intro x y [H1 H2]; apply ltn_0 in H2.
+ intro z IH x y [H1  H2]; case ltn(y,z).
  * intro H.
    have Hz : ltn(x,z); 1: by apply (IH x y _).
   by apply ltn_n_sn x z.
  * intro nH; apply ltn_sn_case in H2; case H2; 1 : auto.
    by rewrite -H2; apply ltn_n_sn.
Qed.

exact lemma [any] of_nat_predn x : x <> zn => of_nat(predn x) = (of_nat x) - (of_int 1).
Proof.
case x; try auto.
intro y _.
rewrite /predn /of_nat.
smt ~no_macros.
Qed.

exact lemma [any] sn_inj a b : a <> b => sn a <> sn b.
Proof.
by intro H [H1].
Qed.


exact lemma [any] gt0 (x,y : nat) : ltn (sn (x),y) => y <> zn.
Proof.
case y.
+ by intro @/ltn H.
+ intro _ _ H; discriminate H.
+ auto. 
Qed.
