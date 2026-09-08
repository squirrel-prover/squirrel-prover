(* ------------------------------------------------------------------- *)
(* Total order on indices *)

(* + We axiomatise an order ~< on the type index,
     that is total, and admits a minimum and a maximum.
   + We then axiomatise predecessor and successor functions,
     that behave as expected strictly between the min and max,
     and loop at each end: succ(max) = max, pred(min) = min.
   + Finally, after defining the system (see `model.sp`), we axiomatise
     that the timestamps that happen are all strictly between min and
     max, and on that interval the order of the trace is the order ~<,
     ie i ~< j => R(i) < R(j). *)

(* ------------------------------------------------------------------- *)

(* strict, total order and its axiomatisation *)
abstract (~<) : index -> index -> bool.

axiom[any] ind_trans (i,j,k:index) : i ~< j => j ~< k => i ~< k.
hint smt ind_trans.

axiom[any] ind_irrefl (i:index) : not (i ~< i).
hint smt ind_irrefl.

axiom[any] ind_tricho (i,j:index) : i ~< j || i = j || j ~< i.
hint smt ind_tricho.


(* zero and max *)
abstract ind_zero : index.
abstract ind_max : index.

axiom[any] ind_zero_min (i:index) : not (i ~< ind_zero).
hint smt ind_zero_min.

axiom[any] ind_max_max (i:index) : not (ind_max ~< i).
hint smt ind_max_max.

axiom[any] ind_diff : ind_zero ~< ind_max.
hint smt ind_diff.

(* ------------------------------------------------------------------- *)

(* predecessor and successor, between min and max *)
abstract ind_pred : index -> index.
abstract ind_succ : index -> index.


axiom[any] ind_pred_order1 (i:index) : ind_zero ~< i => ind_pred i ~< i.
hint smt ind_pred_order1.

axiom[any] ind_pred_order2 (i,j:index) :
  i ~< j => (i = ind_pred j || i ~< ind_pred j).
hint smt ind_pred_order2.


axiom[any] ind_succ_order1 (i:index) : i ~< ind_max => i ~< ind_succ i.
hint smt ind_succ_order1.

axiom[any] ind_succ_order2 (i,j:index) :
  i ~< j => (ind_succ i = j || ind_succ i ~< j).
hint smt ind_succ_order2.


lemma [any] ind_succ_pred (i:index) : ind_zero ~< i => ind_succ (ind_pred i) = i.
Proof.
  smt.
Qed.
hint smt ind_succ_pred.

axiom[any] ind_pred_succ (i:index) : i ~< ind_max => ind_pred (ind_succ i) = i.
hint smt ind_pred_succ.


(* pred 0 = 0, succ max = max *)
axiom[any] ind_pred_zero : ind_pred ind_zero = ind_zero.
hint smt ind_pred_zero.

axiom[any] ind_succ_max : ind_succ ind_max = ind_max.
hint smt ind_succ_max.

(* ------------------------------------------------------------------- *)
(* Element one is the successor of zero *)
op ind_one = ind_succ ind_zero.

lemma [any] ind_o : ind_one = ind_succ ind_zero.
Proof.
  by rewrite /ind_one.
Qed.
hint smt ind_o.

exact axiom [any] ind_pred_one : ind_pred ind_one = ind_zero.
hint rewrite ind_pred_one.

(* ------------------------------------------------------------------- *)

(* The order `~<` is supposed equal to the order by default `<`.
   This is necessary to perform an induction with the order `~<`. *)
axiom [any] ind_to_leq (i,j:index): i ~< j => i < j.



(* ------------------------------------------------------------------- *)

(* Lemmas (not used in proofs, written here as
   sanity checks that the axiomatisation is
   complete enough to let the smt prove interesting things). *)

lemma[any] ind_pred_order3 (i,j:index) :
  ind_zero ~< i => i ~< j => ind_pred i ~< ind_pred j.
Proof. smt. Qed.

lemma[any] ind_succ_order3 (i,j:index) :
  j ~< ind_max => i ~< j => ind_succ i ~< ind_succ j.
Proof. smt. Qed.

lemma[any] ind_pred_inj (i,j:index) :
  ind_zero ~< i => ind_zero ~< j => ind_pred i = ind_pred j => i = j.
Proof. smt. Qed.

lemma[any] ind_succ_inj (i,j:index) :
  i ~< ind_max => j ~< ind_max => ind_succ i = ind_succ j => i = j.
Proof. smt. Qed.

lemma [any] ind_zero_one : ind_zero ~< ind_one.
Proof. smt. Qed.

