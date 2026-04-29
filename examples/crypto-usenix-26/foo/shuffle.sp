include Libs.
include Games.
include[admit] processes.
include NonDeduction.

(*******************************************************************************
# Shuffle opening lemmas.

In this file, we provide the security axiom of shuffle, 
and the generic lemma to open shuffle in the `Privacy_CCA` protocol.

********************************************************************************)


(** The shuffle of an indexed list should not reveal the initial order in the list.
    This idea is modelled by the following axioms `shuffle_rename`, by stating
    that the a shufle of a list is indepedent of the order of its elements.

    In other words, the shuffle of a list l and the shuffle of a permutation 
    of l is the same.
*)

axiom [any] shuffle_rename (f:index -> message) (s : index -> index):
 surjective s =>
 injective s =>
 shuffle f = shuffle (fun i => f (s i)).


lemma [any] shuffle_eq_fun (f:index -> message) (g: index -> message):
(exists s, surjective s && injective s && f = fun i => g (s i))
=> shuffle f = shuffle g.
Proof.
intro H.
destruct H.
destruct H as [Hs Hi H].
rewrite H.
rewrite eq_sym.
apply shuffle_rename; try auto.
Qed.

lemma [any] shuffle_forall_inv_2 (x,y : index) (f : index -> message) :
shuffle f = shuffle (fun z => if z = x then f y 
                            else if (z = y && z <> x) then f x 
                            else if (not (z=x || z =y)) then  f z).
Proof.
apply shuffle_eq_fun.
exists (fun z =>  if z = x then  y 
                            else if (z = y && z <> x) then  x 
                            else if (not (z=x || z = y)) then   z
                            else witness).
repeat split.
+ rewrite /surjective.
  intro b.
  simpl.
  case b = x; case b = y; intro Hx; intro Hy; try auto.
  * by exists x.
  * case y = x; intro Heq; try auto.
    - exists y; smt.
  * by exists x.
  * exists b; smt.
+ rewrite /injective.
  intro i j.
  simpl.
  intro H.
  case i = x; intro Hix; 
  case i = y; intro Hiy; 
  case j = x; intro Hjx;
  case j= y; intro Hjy; smt.
+ apply fun_ext.
  intro a.
  simpl.
  case a = x; intro Hx /=; 
  case a = y; intro Hy /=.
  * by case y = x.
  * by rewrite if_false.
  * rewrite Hx.
    by rewrite Hy.
  * rewrite Hy /=.
    rewrite Hx /=. 
    rewrite if_false; 1:auto. 
    rewrite if_false; 1:auto.
    by rewrite if_true.
Qed.


(* The lemma `open_shuffle` is the generic lemma use to open shuffle.
   
   It is a bi-deducution lemma. For any function `f`
   and conditon `phi`, the lemma show  by 
   bi-deduction the term `if phi then shuffle f` can computed 
   with 
   - two specific images of `f`, `f a` and `f b`.
   - the boolean terms `a=b`
   - the set `{a,b}` modeled by a boolean function testing equality 
     to `a` or `b`
   - the rest of `f` graph
   - `phi`

   The key point in this lemma is that the two terms 
   ` f a` and `f b` will always appear in the 
   same order in the input of the bi-deduction.

*)

global lemma [Privacy_CCA] open_shuffle  
(a0,a1,b0,b1:index) (phi0,phi1:bool)
(f0,f1: index -> message) :
Let a   = diff(a0,a1) in
Let b   = diff(b0,b1) in
Let phi = diff(phi0,phi1) in
Let f   = diff(f0,f1) in 
$(
   (if phi then (fun j => (j=a || j = b)) else (fun (j:index) => false),
    if phi then (a = b) else false,
    if phi then f a,
    if phi then f b,
    if phi then (fun j => (if not ((j=a)||j=b) then f j))
           else (fun (j:index) => zero),
    phi) 
 |>
   (if phi then shuffle f)
).
Proof.
intro a b phi f. 
rewrite /(|>).
exists 
(fun (u: (index -> bool) * bool * message * message * (index -> message) * bool)
  => 
 (let ia = choose (u#1) in
  let ib = choose (fun y => ((u#1) y) && (y <> ia)) in
  if (u#6) then  
  shuffle ( fun x =>
    if x = ia then (u#3) else if (x = ib && x <> ia && (not (u#2))) then (u#4) else (u#5) x))).
simpl.
rewrite /phi.
case diff(phi0,phi1); try by rewrite if_false0.
intro Hphi.
rewrite !if_true0.
assert (choose (fun (j:index) => j =a || j =  b) =  a  ||
choose (fun (j:index) => j = a || j = b) =  b )
by apply choose_or.
case H; try rewrite H;
case a = b ; intro HCase; try rewrite HCase.
* rewrite !or_double => //. 
  simpl.
  assert forall f g, ((f = g) => (shuffle f = shuffle g)) as Hs
  by auto.
  apply Hs. 
  apply fun_ext.
  intro y.
  reduce.  
  by case (y = b).
* assert 
  choose (fun (y:index) =>  (y =  a || y =  b) && y <>  a) = b.
  by apply choose_or_not. 
  rewrite Ieq.
  simpl.
  assert forall f g, ((f = g) => (shuffle f = shuffle g)) as Hs
  by auto.
  apply Hs. 
  apply fun_ext.
  intro y.
  reduce.  
  case (y = a); try auto.
  intro neqa.
  simpl.
  search if (_ && _ ) then _ else _.
  rewrite -if_then_then. simpl.
  case y = b; try auto.
  intro eqb.
  simpl.
  rewrite if_true. auto.
  by rewrite eqb.
* rewrite !or_double => //. 
  simpl.
  assert forall f g, ((f = g) => (shuffle f = shuffle g)) as Hs
  by auto.
  apply Hs. 
  apply fun_ext.
  intro y.
  reduce.  
  by case (y = b).  
* assert 
  choose (fun (y:index) =>  (y =  a || y =  b) && y <>  b) = a.
  rewrite or_comm.
  by apply choose_or_not.
  rewrite Ieq.  
  simpl.
  rewrite eq_sym.
  rewrite or_comm.
  apply shuffle_forall_inv_2.    
Qed.
