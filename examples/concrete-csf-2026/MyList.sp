include Concrete.
include MyNat.

(* type of the element of a list, must be finite fixed, to be an
   indices of a name, in the birthday paradox *)
type lval[serializable,finite,fixed].

(* option type *)
inductive o_lval =
| l_none : o_lval
| l_some : lval -> o_lval.

let oget (x : o_lval) with
| l_none -> witness
| l_some y -> y.

(* definition of the list type *)
inductive mylist =
| MEmp : mylist
| MCons : lval -> mylist -> mylist.

(* basic functions on list type *)
let rec length (l : mylist) with
| MEmp -> zn
| MCons _ l -> sn (length l).
Proof. intro > <-; discriminate. Qed.

let rec in_list (a : lval) (l : mylist) with
| MEmp -> false
| MCons b l -> (a = b) || (in_list a l).
Proof. intro > <- _; discriminate. Qed.

let rec get (n : nat) (l : mylist) : o_lval with
| MEmp -> l_none
| MCons a l ->
if ltn (n,zn) then l_none else (if ltn (zn,n) then get (predn n) l else  l_some a).
Proof.
    intro > <- _ _; discriminate.
Qed.

(* basic lemmas *)
exact lemma [any] length_empty (l : mylist) : length l = zn => l = MEmp.
Proof.
case l; 1:  auto.
+ intro h l0; intro H; discriminate H.
+ auto. 
Qed.

exact lemma [any] empty_length (l : mylist) : l = MEmp => length l = zn.
Proof.
case l; 1:  auto.
+ intro h l0; intro H; discriminate H.
+ auto. 
Qed.

exact lemma [any] get_in_cons (h : lval) (t : mylist) (n : nat) :
    get n t = get (sn n) (MCons h t).
Proof.
generalize h n.
induction t.
+ intro h k; rewrite /get /ltn //=.
+ intro h t IH h0 k.
   case k; 1: auto.
    intro k0; rewrite /get //=.
    auto.
Qed.

exact lemma [any] get_in_range (l : mylist) :
    forall(n : nat),
        ltn (n,(predn (length l))) && l <> MEmp => get n l <> l_none.
Proof.
induction ~general l => l.
case l.
+ by intro H n [H1 H2].
+ intro h t IH n [H1 H2]; revert H1.
    case n.
    ++ rewrite /get /ltn //= => _ H_; discriminate H_.
    ++ intro n0 H1.
        rewrite /length /predn //= in H1.
        set alpha := t. have Htemp : alpha = t; 1 : auto.
        revert Htemp.
        case t.
        +++ intro Ht; rewrite Ht //= in H1.
        +++ intro h0 t0 Ht. rewrite /alpha in Ht; rewrite Ht /get /ltn //= /predn.
                revert H1; case n0.
                * intro H1; rewrite /get /ltn //=; intro H_; discriminate H_.
                * intro x H1; rewrite /get /ltn //= /predn. apply IH.
                    ** rewrite Ht; discriminate.
                    ** rewrite Ht /length /ltn in H1.
                        have Ht0 : t0 <> MEmp.
                        - by intro Htemp; apply empty_length in Htemp; rewrite Htemp in H1.
                        - split; 2 : assumption. clear alpha.
                          set alpha := length t0. have Htemp : alpha = length t0; 1 : auto. revert Htemp.
                          case (length t0); 1 : intro H; rewrite H //= in H1.
                         intro x0 H; rewrite H /predn; rewrite /alpha in H; rewrite H //= in H1.
        auto. * auto. +++ auto. ++ auto. + auto. 
Qed.

