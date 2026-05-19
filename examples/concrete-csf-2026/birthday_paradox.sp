include Concrete. include MyNat. include MyList.
open FiniteTypes.
open Int.
open Real.
system P = null.

(*Sampling function *)
name n : lval -> lval.

(*Prediate stating that a list does not contain any duplicate
    if two position `a` and `b` are in the range of the list and not equal then
    the element at those position are also not equal
*)
predicate NoDuplicates {set : system} {set : (l : mylist)} =
    Forall (a,b : nat[const]),
        [ltn (a,(length l)) <: z] /\ [ltn (b,(length l))  <: z]
         -> [a <> b => get a l <> get b l <: z].

(*Map function that take a list and apply n to each element*)
let rec map (l :mylist) with
| MEmp -> MEmp
| MCons m l -> MCons (n m) (map l).
Proof.
intro > <-; discriminate.
Qed.

(* `true` iff. there a no collision in list of indices `l` with the
   `n` name*)
let rec no_collision (l : mylist) with
| MEmp -> true
| MCons m l -> no_collision l && not (in_list (n m) (map l)).
Proof.
intro > <-; discriminate.
Qed.


global lemma [any] case_list_const (l : mylist[const]) :
    [l = MEmp <: z] \/ 
    Exists(h : lval[const], t : mylist[const]), 
    [l = MCons h t <: z].
Proof.
   case l; [ 1: by left | 2: by intro h t; right; exists h; exists t].
Qed.

(* ------------------------------------------------------------------- *)
(* Lemmas on the `NoDuplicates` predicate *)

global lemma [any] no_duplicates_cons (h : lval) (t : mylist) :
     NoDuplicates (MCons h t) -> NoDuplicates t.
Proof.
   intro @/NoDuplicates H_ a b [H1 H2]. intro H'.
   rewrite (get_in_cons h) (get_in_cons h _ b).
   apply H_; 1 : split; by rewrite /length /ltn.
   by apply sn_inj.
Qed.

global lemma no_duplicates_cons_in @system:P (h : lval) (t : mylist[const]) :
     NoDuplicates (MCons h t) -> [not(in_list h t ) <: z].
Proof.
generalize h.
induction ~general t => t IH h.
have [ H | [h0 [t0 H]] ] := case_list_const t; rewrite !H.
+ reduce ~delta; intro > _; auto.
+ intro H_; have H__ := no_duplicates_cons _ _ H_.
   have neqhh0 : h <> h0.
   ++ intro Heq. rewrite /NoDuplicates in H_.
        have H1 := H_ zn (sn zn) _ _; [1 : intro Hzn ; discriminate Hzn | 2 : by split].
        ghave H2 :  [get zn (MCons h (MCons h t0)) = get (sn zn) (MCons h (MCons h t0)) <: z]; auto.
   ++ rewrite /in_list //= not_or; split; 1 : auto.
        apply IH; 2 : rewrite H; discriminate.
        rewrite /NoDuplicates. intro n1 n2.
        case ~tags n1.
        * case ~tags n2; try (intro _; auto).
           intro [Hleq1 Hleq2] @/get @/ltn //= . rewrite /NoDuplicates in H_.
           have Hx := localize(H_ zn (sn (sn x)) _) _; [1:  intro temp; discriminate temp | 3 : auto].
            split.
            ** rewrite (ltn_trans _ (length (MCons h t0))); 2 : auto. split ; 1 :auto. rewrite /length /ltn /length.
                induction length t0; auto.
            ** by rewrite /length /ltn.
        * case ~tags n2; try auto.
           ** intro _ @/get @/ltn //= . rewrite /NoDuplicates in H_.
                have Hx := localize(H_ (sn (sn x)) zn _) _; [1:  intro temp; discriminate temp | 3 : auto]. split.
                *** by rewrite /length /ltn.
                *** rewrite (ltn_trans _ (length (MCons h t0))); 2 : auto. split ; 1 :auto. rewrite /length /ltn /length.
                       induction length t0; auto.
            **  intro _ _ @/get @/ltn //= . rewrite /NoDuplicates in H_.
                have Hx := localize(H_ (sn (sn x)) (sn (sn x0)) _) _; [1:  by apply sn_inj| 3 : auto].
                *** by rewrite /length /ltn.
Qed.

(* ------------------------------------------------------------------- *)
(*Show that `n x` is in the list `map l` only if `x` is in the list `x` upto
small error probabily*)
global lemma [P] col_list (x : lval[const]) (l : mylist[const]) :
    [in_list (n x) (map l) => in_list x l
     <: (Real.of_nat (length l)) * proba_fresh[lval]].
Proof.
   induction ~general l.
   intro l IH.
   have [Hl | [ h t Hl]] := case_list_const l.
   + rewrite !Hl; auto.
   + rewrite !Hl; reduce ~delta; intro [ H <: proba_fresh[lval] | H ].
     * by left; fresh H.
     * right. apply IH; 1:  rewrite Hl; discriminate.
       weak z; 1: (smt ~no_macros (* basic algebraic reasoning *)).
       assumption.
Qed.

global lemma [P] birthday (l : mylist[const]) :
    NoDuplicates l ->
    [no_collision l
     <: Real.div 
          (  Real.of_nat (length l)
           * Real.of_nat (predn (length l)))
          (Real.of_int 2)
        * proba_fresh[lval]].
Proof.
  induction ~general l.
  intro l IH.
  have [Hl | [ h t Hl]] := case_list_const l. {
    intro _; rewrite !Hl; auto.
  }.
  rewrite !Hl=> Hu.
  rewrite /no_collision.
  split (div (of_nat (length t) * of_nat( predn (length t))) (of_int 2) )* proba_fresh[lval].
  + apply IH.
    - apply no_duplicates_cons _ _ Hu.
    - rewrite Hl; discriminate.
    - auto.
  + rewrite /= /length /predn //=.
    weak (Real.of_nat (length t)*proba_fresh[lval]).
    - rewrite /div -mul_distrib_minus -mul_distrib_minus
              (Real.mul_comm _ (of_nat (predn( length t )))) -mul_distrib_minus.
      case (length t = zn).
      * intro -> //. 
      * intro H.
        have [x Hlt] : exists x, length t = sn x. {
          revert H.
          case length t; [1: auto | 2: by intro x _; exists x | 3: auto].
        }.
        clear H. 
        rewrite !Hlt //= /of_nat /of_nat of_nat_predn.
        ** intro H; discriminate H.
        ** rewrite !(Real.add_comm (of_int 1)) !Real.add_assoc //=. 
           smt ~no_macros.
    - intro H.
      have Hin : in_list h t <: (Real.of_nat (length t))* proba_fresh[lval]; 1 : by apply col_list.
      by have _ := no_duplicates_cons_in h t Hin.
Qed.
