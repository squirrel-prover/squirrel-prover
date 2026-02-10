include Core.

(* ------------------------------------------------------------------- *)
(* Some `if then else` rewriting lemma*)

lemma [any] leq_leq (x,y:timestamp) : (x < y && y < x) = false. 
Proof.
case x < y; case y < x => //.
Qed.

lemma [any] if_then_then_inv  (b,b':bool) (x : message) :
if b then (if b' then x) = if b' then (if b then x).
Proof. 
  rewrite 2!if_then_then and_comm.
  apply eq_refl.
Qed.

lemma [any] if_then_push (b:bool) (x:message) :
if b then x = if b then (if b then x).
Proof.
  auto. 
Qed.

lemma [any] if_then_then_else_not ['a ]  (b,b' : bool) (x,y,z:message) :
  if b then x else if b' then y else if not (b || b') then z = 
  if b then x else if b' then y else z.
Proof.
  fa => //.
  intro Hb /=.
  fa => //.
  intro Ib. 
  rewrite if_true // not_or.
Qed.

lemma [any] if_then_then_else_not_app ['a ]  (b,b' : 'a -> bool) (x,y,z:message) :
  forall a,
  if b a then x else if b' a then y else if not (b a || b' a) then z = 
  if b a then x else if b' a  then y else z.
Proof.
  intro a.
  fa => //.
  intro Hb /=. 
  fa => //.
  intro Ib.
  rewrite if_true // not_or.
Qed.

lemma [any] if_then_then_else_inv ['a] (b,b' : 'a -> bool) (x,y,z : message) :
   forall a,
   ((b a => not (b' a)) && (b' a => not (b a))) =>
   if b a then x else if b' a then y else z =
   if b' a then y else if b a then x else z.
Proof.
  intro a.
  intro [H0 H1].
  case (b a); 2:auto.
  intro H. 
  rewrite /= if_false //. 
Qed. 

(* ------------------------------------------------------------------- *)
(* Implication rewriting *)
lemma [any] impl_true (b,c:bool) : b => ((b => c) = c).
Proof.
  intro *.
  case b ; case c; intro ?? //.
Qed.

(* ------------------------------------------------------------------- *)
(* Function rewriting axiom and lemmas *)

lemma [any] fun_ext_l ['a 'b] (f1,f2 : 'a -> 'b ) :
  f1 = f2 => forall a, f1 a = f2 a.
Proof.
  by intro ->.
Qed.

lemma [any] fun_eta ['a 'b] (f:'a -> 'b) :
  f = fun x => f x.
Proof.
  by apply fun_ext.
Qed.

lemma [any] fun_eta_app ['a 'b] (f : 'a -> 'b) (a:'a) :
  f a = (fun x => f x) a.
Proof.
  by rewrite fun_eta.
Qed.

lemma [any] choose_fun ['a 'b] (f : 'a -> 'b) (phi : 'b -> bool) :
  (exists j, phi (f j)) => 
  phi (f (choose (fun y => phi (f y)))).
Proof.
  intro [j H].
  apply choose_spec (fun y => phi (f y)) j. 
  apply H.
Qed.

lemma [any] if_then_else_fun ['a ] (b : bool) (x: 'a -> bool) : 
  (fun j => if b then x j else false) = 
  if b then (fun j => x j) else (fun _ => false). 
Proof.
  case b ; intro H.
  rewrite !if_true0.
  by apply fun_ext.
  rewrite !if_false0.
  by apply fun_ext.
Qed.

(* ------------------------------------------------------------------- *)
(* choose rewriting lemma *)

lemma [any] choose_or ['a] (x,y : 'a) :
  choose (fun z => z = x || z = y) = x ||
  choose (fun z => z = x || z = y) = y.
Proof.
  have -> : 
    (choose (fun (z:'a) => z = x || z = y) = x ||
     choose (fun (z:'a) => z = x || z = y) = y) = 
    (fun z => (z = x || z = y)) (choose (fun (z:'a) => z = x || z = y)).
    by reduce.
  by rewrite (choose_spec (fun z => z = x || z = y) x ).
Qed.

lemma [any] choose_or_not ['a] (x,y : 'a) :
  let b = (fun z => (z = x || z = y)&& z <> x) in
  x <> y => 
  choose b = y.
Proof.
  intro b H.
  have H0 : (forall z, b z => (z = y)). {
    intro z Heq.
    rewrite /b in Heq; destruct Heq.
    case H0 => //.  
  }.
  apply H0.
  
  rewrite /*.
  rewrite (choose_spec (fun z => (z = x || z = y) && z <>x) y). {
    by rewrite neq_sym.
  }.
  auto.
Qed.

lemma [any]  choose_eq ['a] (a,b : 'a -> bool) :
  choose a = choose b =>
  (( forall j, not (a j)) || (forall j, not (b j))) || exists j, a j && b j.
Proof.
  intro Heq.
  case (forall (j:'a), not (a j)) || forall (j:'a), not (b j) ; intro H.
  + by left.
  + right.
    rewrite not_or !not_forall_1 //= in H.
    destruct H as [[a0 Ha] [a1 Hb]].
    exists choose a.
    split.  
    - by apply choose_spec a a0.
    - rewrite Heq.  
      by apply choose_spec b a1.
Qed.

lemma[any] choose_eq_direct ['a] (a,b : 'a -> bool) :
  (exists j, a j) => 
  (exists j, b j) => 
  (forall i j, (a i && b j) => i = j) => 
  choose a = choose b.
Proof. 
  intro *.
  have -> := H1 (choose a) (choose b); 2:auto.
  split.
  + have Ha /= := choose_fun (fun (x:'a) => x) a.
    have Meq : (fun y => a y) = a by apply fun_ext.
    rewrite Meq in Ha.
    apply Ha.
    by apply H. 
  + have Hb /= := choose_fun (fun (x:'a) => x) b.
    have Meq : (fun y => b y) = b by apply fun_ext.
    rewrite Meq in Hb.
    apply Hb.
    by apply H0. 
Qed.

lemma [any] rewrite_fun_eq ['a 'b]
(f: 'a -> 'b) (a,a' : 'a) (b:'b):
(a = a') => (f a = b) => (f a' = b).
Proof.
intro *.
by rewrite -Meq.
Qed.

lemma [any] choose_ex ['a] :
forall (phi : 'a -> bool), (exists a, phi a) => phi (choose phi).
Proof.
intro *.
destruct H.
by apply choose_spec phi a.
Qed.


lemma [any] if_push_add ['a] (b:bool) (u:'a): 
u = if b then (if b then u else witness) else (if not b then u else witness).
Proof.
by case b.
Qed.

lemma [any] and_if (b1,b2:bool): 
(b1 && b2) = if b2 then b1 else false.
Proof.
by (case b1;case b2).
Qed.

lemma [any] boolean_eq (b,b':_) : 
((b => b')&&(b' => b)) => (b=b').
Proof.
intro [H1 H2].
case b; intro Hb; try auto.
case b'; intro Hb'; try auto.
Qed.

(* ------------------------------------------------------------------- *)
axiom [any] leq_index_total (i,j:index) : i <= j || j <= i.

axiom [any] lt_index_total (i,j:index) : i < j || j < i || i = j.
