(*------------------------------------------------------------------*)
(* equality *)

axiom [any] eq_iff (x, y : boolean) : (x = y) = (x <=> y).

axiom [any] eq_not (x, y : boolean) : (not(x) = not(y)) = (x = y).

lemma [any] eq_sym ['a] (x,y : 'a) : (x = y) = (y = x).
Proof. by rewrite eq_iff. Qed.

lemma [any] neq_sym ['a] (x,y : 'a) : (x <> y) = (y <> x).
Proof. by rewrite eq_iff. Qed.

lemma [any] eq_refl_e ['a] (x : 'a) : (x = x) = true.
Proof.
  by rewrite eq_iff.
Qed.
hint rewrite eq_refl_e.

lemma [any] eq_refl ['a] (x : 'a) : x = x.
Proof. 
  by rewrite eq_refl_e.
Qed.

lemma [any] neq_irrefl ['a] (x : 'a) : (x <> x) <=> false.
Proof. by split. Qed.
hint rewrite neq_irrefl.


lemma [any] eq_assoc (b0,b1,b2: boolean) : ((b0 = b1) = b2) = (b0 = (b1 = b2)).
Proof. 
(* smaller proof if put after section true/false *)
assert((true = false) = false) as true_false by rewrite eq_iff.
assert((false = true) = false) as false_true by rewrite eq_iff.
case b0; case b1; case b2; try auto. by rewrite true_false. by rewrite false_true. 
Qed.
 


(*------------------------------------------------------------------*)
(* true/false *)

lemma [any] true_false : (true = false) = false.
Proof. by rewrite eq_iff. Qed.
hint rewrite true_false.

lemma [any] false_true : (false = true) = false.
Proof. 
  by rewrite (eq_sym false true).
Qed.
hint rewrite false_true.

lemma [any] eq_true (b:boolean) : (b = true) = b.
Proof. by case b. Qed.
hint rewrite eq_true.

lemma [any] eq_true2 (b:boolean) : (true = b) = b.
Proof. by case b. Qed.
hint rewrite eq_true2.

(*------------------------------------------------------------------*)
(* not *)

axiom [any] not_true : not(true) = false.
hint rewrite not_true.

axiom [any] not_false : not(false) = true.
hint rewrite not_false.


lemma [any] not_not (b : boolean): not (not b) = b.
Proof.
  by case b.
Qed.
hint rewrite not_not.

lemma [any] not_eq ['a] (x, y : 'a): not (x = y) = (x <> y).
Proof. 
by rewrite eq_iff. 
Qed.
hint rewrite not_eq.

lemma [any] not_neq ['a] (x, y : 'a): not (x <> y) = (x = y).
Proof. 
by rewrite eq_iff. 
Qed.
hint rewrite not_neq.

lemma [any] not_eqfalse (b:boolean) : (b = false) = not(b).
Proof.
 by case b.
Qed.

lemma [any] not_impl (a, b:bool) : not (a => b) = (a && not b).
Proof.
  rewrite eq_iff; split; intro H.
  + split. 
    * rewrite -not_not.
      intro Hna.
      by apply H.
    * intro Hb.
      by apply H.
  + intro Hi.
    destruct H as [Ha Hnb].
    apply Hnb.
    by apply Hi.
Qed.

(*------------------------------------------------------------------*)
(* disequality *)

lemma [any] eq_false ['a] (x, y : 'a): ((x = y) = false) = (x <> y).
Proof. 
rewrite -not_eq. case (x = y) => _. simpl. auto.
by rewrite eq_iff. 
Qed.
hint rewrite eq_false.

(*------------------------------------------------------------------*)
(* and *)

axiom [any] and_comm (b,b' : boolean) : (b && b') = (b' && b).

lemma [any] and_dist (b0,b1,b2: boolean) : ((b0 || b1) && b2) = ((b0 && b2) || (b1 && b2)).
Proof. rewrite eq_iff. by split. Qed.

axiom [any] and_true_l (b : boolean) : (true && b) = b.
hint rewrite and_true_l.

lemma [any] and_true_r (b : boolean) : (b && true) = b.
Proof. by rewrite and_comm and_true_l. Qed.
hint rewrite and_true_r.

axiom [any] and_false_l (b : boolean) : (false && b) = false.
hint rewrite and_false_l.

lemma [any] and_false_r (b : boolean) : (b && false) = false.
Proof. by rewrite and_comm and_false_l. Qed.
hint rewrite and_false_r.


lemma [any] and_double (b:boolean) : (b && b) = b.
Proof.  by case b. Qed.


(*------------------------------------------------------------------*)
(* or *)
axiom [any] or_comm (b,b' : boolean) : (b || b') = (b' || b).

lemma [any] or_dist (b0,b1,b2: boolean) : ((b0 || b2) && (b1 || b2)) =  ((b0 && b1) || b2).
Proof. rewrite eq_iff. by split. Qed.

axiom [any] or_false_l (b : boolean) : (false || b) = b.
hint rewrite or_false_l.

lemma [any] or_false_r (b : boolean) : (b || false) = b.
Proof. by rewrite or_comm or_false_l. Qed.
hint rewrite or_false_r.

axiom [any] or_true_l (b : boolean) : (true || b) = true.
hint rewrite or_true_l.

lemma [any] or_true_r (b : boolean) : (b || true) = true.
Proof. by rewrite or_comm or_true_l. Qed.
hint rewrite or_true_r.

lemma [any] or_double (b:boolean) : (b || b) = b.
Proof. by case b. Qed.


(*------------------------------------------------------------------*)
(* impl *)
lemma [any] impl_charac (b,b' : boolean) : (b => b') = ((not b) || b').
Proof. 
  rewrite eq_iff; split; case b; case b' => //=. 
Qed.

lemma [any] impl_false_l (b : boolean) : (false => b) = true.
Proof. by rewrite eq_iff; case b. Qed.
hint rewrite impl_false_l.

lemma [any] impl_true_r (b : boolean) : (b => true) = true.
Proof. auto. Qed.
hint rewrite impl_true_r.

lemma [any] impl_true_l (b: boolean) : (true => b) = b.
Proof. by rewrite eq_iff. Qed.
hint rewrite impl_true_l.

lemma [any] impl_contra (b,c:boolean) : (b => c) = (not c => not b).
Proof.
  rewrite !impl_charac /=.
  by rewrite or_comm.
Qed.

(*------------------------------------------------------------------*)
(* not: more lemmas *)

lemma [any] not_and (a, b : boolean): not (a && b) = (not a || not b).
Proof. 
  rewrite eq_iff. 
  case a; case b => //=.
Qed.

lemma [any] not_or (a, b : boolean): not (a || b) = (not a && not b).
Proof. 
  rewrite eq_iff. 
  case a; case b => //=.
Qed.

(*------------------------------------------------------------------*)
(* if *)

lemma [any] if_true ['a] (b : boolean, x,y : 'a):
  b => if b then x else y = x.
Proof.
  intro *.
  case (if b then x else y).
  + auto.
  + intro [HH _]. by use HH.
Qed.

lemma [any] if_true0 ['a] (x,y : 'a):
  if true then x else y = x.
Proof.
  by rewrite if_true. 
Qed.
hint rewrite if_true0.

lemma [any] if_false ['a] (b : boolean, x,y : 'a):
  (not b) => if b then x else y = y.
Proof. 
  intro *; case (if b then x else y).
  + intro [H1 H2]. 
    by rewrite H1 in H2. 
  + auto.
Qed.

lemma [any] if_false0 ['a] (x,y : 'a):
  if false then x else y = y.
Proof.
  by rewrite if_false.
Qed.
hint rewrite if_false0.

lemma [any] if_then_then ['a] (b,b' : boolean, x,y : 'a):
  if b then (if b' then x else y) else y = if (b && b') then x else y.
Proof.  
  by case b; case b'.
Qed.

lemma [any] if_then_or (b0,b1: boolean, m0,m1:message): 
  if b0 then m0 else (if b1 then m0 else m1) = if b0 || b1 then m0 else m1.
(* It would have been more logical to call it if_then_else to match the name if_then_then,
   but if_then_else is a pretty bad name so I used if_then_or *)
Proof. 
assert(b0 || not(b0)) as [_|_] by auto. rewrite if_true => //. rewrite if_true => //. 
assert(b1 || not(b1)) as [_|_] by auto. rewrite if_false => //. rewrite !if_true => //. 
rewrite !if_false => //.
Qed.

lemma [any] if_then_implies ['a] (b,b' : boolean, x,y,z : 'a):
  if b then (if b' then x else y) else z =
  if b then (if b => b' then x else y) else z.
Proof.
  case b; intro H; case b'; intro H'; simpl; try auto.  
Qed.

lemma [any] if_same ['a] (b : boolean, x : 'a):
  if b then x else x = x.
Proof.
  by case b.
Qed.
hint rewrite if_same.

lemma [any] if_then ['a] (b,b' : boolean, x,y,z : 'a):
 b = b' => 
 if b then (if b' then x else y) else z = 
 if b then x else z.
Proof.
  by intro ->; case b'.
Qed.
hint rewrite if_then.

lemma [any] if_then_inv (b:boolean, m0,m1:message): 
  if b then m0 else m1 = if b then (if b then m0) else m1.
  (* More practical than the previous lemma when you want to expand. *)
Proof. auto. Qed.

lemma [any] if_else ['a] (b,b' : boolean, x,y,z : 'a):
 b = b' => 
 if b then x else (if b' then y else z) = 
 if b then x else z.
Proof.
  by intro ->; case b'.
Qed.
hint rewrite if_else.

lemma [any] if_else_inv (b:boolean, m0,m1:message):
  if b then m0 else m1 = if b then m0 else (if not b then m1).
Proof. by case b. Qed.

lemma [any] if_push (b:boolean, m0,m1:message):
  if b then m0 else m1 = if b then (if b then m0) else (if (not b) then m1).
Proof. by rewrite if_else_inv if_then_inv. Qed.

lemma [any] if_then_not ['a] (b,b' : boolean, x,y,z : 'a):
 b = not b' => 
 if b then (if b' then x else y) else z = 
 if b then y else z.
Proof.
  by intro ->; case b'.
Qed.
hint rewrite if_then_not.

lemma [any] if_else_not ['a] (b,b' : boolean, x,y,z : 'a):
  b = not b' => 
 if b then x else (if b' then y else z) = 
 if b then x else y.
Proof.  
  by intro ->; case b'.
Qed.
hint rewrite if_else_not.

lemma [any] if_app ['a 'b] (f:'a->'b) (c:bool) (x,y:'a) :
  f (if c then x else y) = if c then f x else f y.
Proof. by case c. Qed.

(*------------------------------------------------------------------*)
(* some functional properties *)

lemma [any] fst_pair (x,y : message) : fst (<x,y>) = x.
Proof. auto. Qed.
hint rewrite fst_pair.

lemma [any] snd_pair (x,y : message) : snd (<x,y>) = y.
Proof. auto. Qed.
hint rewrite snd_pair.

(*------------------------------------------------------------------*)
(* if-and-only-if *)

lemma [any] iff_def (x,y : boolean) : (x <=> y) = ((x => y) && (y => x)).
Proof. 
 rewrite eq_iff; split.
 by intro ->. 
 auto.
Qed.

lemma [any] iff_refl (x : boolean) : (x <=> x) = true.
Proof.
 by rewrite eq_iff. 
Qed.
hint rewrite iff_refl.

lemma [any] iff_sym (x, y: boolean) : (x <=> y) = (y <=> x).
Proof.
 by rewrite eq_iff !iff_def.
Qed.

lemma [any] true_iff_false : (true <=> false) = false.
Proof.
 by rewrite -eq_iff. 
Qed.
hint rewrite true_iff_false.

lemma [any] false_iff_true : (false <=> true) = false.
Proof.
 by rewrite -eq_iff. 
Qed.
hint rewrite false_iff_true.


lemma [any] contra_iff (x, y : boolean) : ((not x) <=> y) = (x <=> (not y)).
Proof.
  rewrite eq_iff.
  split; by rewrite !-eq_iff -eq_not.
Qed.

(*------------------------------------------------------------------*)
(* exists *)

lemma [any] exists_false1 ['a]:
(exists (a:'a), false) = false.
Proof. by rewrite not_eqfalse. Qed.

lemma [any] exists_false2 ['a 'b]:
(exists (a:'a, b:'b), false) = false.
Proof. by rewrite not_eqfalse. Qed.

lemma [any] exists_false3 ['a 'b 'c]:
(exists (a:'a, b:'b, c:'c), false) = false.
Proof. by rewrite not_eqfalse. Qed.

lemma [any] exists_false4 ['a 'b 'c 'd]:
(exists (a:'a, b:'b, c:'c, d:'d), false) = false.
Proof. by rewrite not_eqfalse. Qed.

lemma [any] exists_false5 ['a 'b 'c 'd 'e]:
(exists (a:'a, b:'b, c:'c, d:'d, e:'e), false) = false.
Proof. by rewrite not_eqfalse. Qed.

lemma [any] exists_false6 ['a 'b 'c 'd 'e 'f]:
(exists (a:'a, b:'b, c:'c, d:'d, e:'e, f:'f), false) = false.
Proof. by rewrite not_eqfalse. Qed.



(*------------------------------------------------------------------*)
(* forall *)


lemma [any] forall_true1 ['a]:
(forall (a:'a), true) = true.
Proof. auto. Qed.

lemma [any] forall_true2 ['a 'b]:
(forall (a:'a, b:'b), true) = true.
Proof. auto. Qed.

lemma [any] forall_true3 ['a 'b 'c]:
(forall (a:'a, b:'b, c:'c), true) = true.
Proof. auto. Qed.

lemma [any] forall_true4 ['a 'b 'c 'd]:
(forall (a:'a, b:'b, c:'c, d:'d), true) = true.
Proof. auto. Qed.

lemma [any] forall_true5 ['a 'b 'c 'd 'e]:
(forall (a:'a, b:'b, c:'c, d:'d, e:'e), true) = true.
Proof. auto. Qed.

lemma [any] forall_true6 ['a 'b 'c 'd 'e 'f]:
(forall (a:'a, b:'b, c:'c, d:'d, e:'e, f:'f), true) = true.
Proof. auto. Qed.


(*------------------------------------------------------------------*)
(* length *)

axiom [any] len_zeroes (x:message) : len(zeroes(x)) = len(x).
hint rewrite len_zeroes.


(*------------------------------------------------------------------*)
(* exec and cond *)

(* Squirrel can only expand exec for specific actions.
   This axiom allows to go beyond this. It would be provable
   in any system, by performing a case analysis on tau. *)
axiom [any] exec_not_init (tau:timestamp) :
  init < tau => exec@tau = (exec@pred(tau) && cond@tau).

axiom [any] exec_init (tau:timestamp) : tau = init => exec@tau = true.
axiom [any] cond_init (tau:timestamp) : tau = init => cond@tau = true.

lemma [any] exec_le (tau,tau':timestamp) : tau' <= tau => exec@tau => exec@tau'.
Proof.
  induction tau => tau IH Hle Hexec.
  case (tau = tau').
  + auto.
  + intro Hneq.
    rewrite exec_not_init // in Hexec.
    by apply IH (pred(tau)).
Qed.

lemma [any] exec_cond (tau:timestamp) : happens(tau) => exec@tau => cond@tau.
Proof.
  intro Hap Hexec.
  case (init < tau) => _.
  - by rewrite exec_not_init in Hexec.
  - by rewrite cond_init.
Qed.

(*------------------------------------------------------------------*)

lemma [any] f_apply ['a 'b] (f : 'a -> 'b) (x, y : 'a) : x = y => f x = f y.
Proof. by intro ->. Qed.

lemma [any] not_exists_1 ['a] (phi:'a -> bool) :
 not (exists (a:'a), phi a) = forall (a:'a), not (phi a).
Proof.
  rewrite eq_iff.
  split.
  + intro H a Hp.
    apply H. 
    by exists a.
  + intro H [a Hp]. 
    by use H with a.
Qed.

lemma [any] not_exists_2 ['a 'b] (phi:'a -> 'b -> bool) :
 not (exists (a:'a, b:'b), phi a b) = forall (a:'a, b:'b), not (phi a b).
Proof.
  rewrite eq_iff.
  split.
  + intro H a b Hp.
    apply H. 
    by exists a,b.
  + intro H [a b Hp]. 
    by use H with a, b.
Qed.

axiom [any] not_forall_1 ['a] (phi:'a -> bool) :
 not (forall (a:'a), phi a) = exists (a:'a), not (phi a).

axiom [any] not_forall_2 ['a 'b] (phi:'a -> 'b -> bool) :
 not (forall (a:'a, b:'b), phi a b) = exists (a:'a, b:'b), not (phi a b).

(*------------------------------------------------------------------*)

(** Choose takes a predicate and returns an element that satisfies it,
    if one exists. Otherwise it returns an arbitrary element. This
    is possible because types cannot be empty in our logic.
    Introducing choose gives as a way to denote an inhabitant of
    each type as, namely as (choose (fun _ => false)). *)
abstract choose ['a] : ('a -> bool) -> 'a.

axiom [any] try_carac_1 ['a 'b] (phi:'a->bool) (f:'a->'b) (g:'b) :
  (try find x such that phi x in f x else g) =
  (if exists x, phi x then f (choose phi) else g).

lemma [any] choose_spec ['a] (phi:'a->bool) (x:'a) :
  phi x =>
  phi (choose phi).
Proof.
  intro H.
  assert
    phi (choose phi) = if exists x, phi x then phi (choose phi) else false
    as ->.
  {.
    rewrite if_true => //. by exists x.
  }.
  rewrite -(try_carac_1 phi phi false).
  case ~struct (try find x such that phi x in phi x else false).
  + auto.
  + intro [HH _]; by use HH with x.
Qed.

(** The try find construct chooses witnesses following the choose function. *)
lemma [any] try_choose ['a 'b] (phi:'a->bool) (f:'a->'b) (g:'b) (x:'a) :
  phi x =>
  (try find x such that phi x in f x else g) =
  (f (choose phi)).
Proof.
  intro H.
  rewrite try_carac_1.
  rewrite if_true => //.
  by exists x.
Qed.

(** Quantifier commutations. *)

lemma [any] forall_exists ['a 'b] (phi:'a->'b->bool) :
  (forall x:'a, exists y:'b, phi x y) =
  (exists y':'a->'b, forall x:'a, phi x (y' x)).
Proof.
  rewrite eq_iff; split.
  + intro H.
    exists (fun x => choose (fun y => phi x y)).
    intro x; simpl.
    have [y Hy] := H x.
    (* Perform beta-expansion before applying choose_spec. *)
    assert (phi x (choose (fun y => phi x y)) =
            (fun y => phi x y) (choose (fun y => phi x y)))
      as -> by auto.
    apply choose_spec _ y.
    simpl; assumption.
  + intro [y' H] x.
    exists (y' x).
    by apply H.
Qed.

lemma [any] implies_exists ['a] (phi:bool,psi:'a->bool) :
  (phi => exists j:'a, psi(j)) =
  (exists x:'a, phi => psi(x)).
Proof.
  rewrite eq_iff; split.
  + intro H.
    case phi.
    * intro phi.
      assert exists x, psi x as [x _] by apply H.
      by exists x.
    * intro _.
      by exists (choose (fun _ => false)).
  + intro [x H] H'.
    by exists x.
Qed.

(*------------------------------------------------------------------*)
(* Order *)

axiom [any] le_trans    ['a] (x,y,z : 'a) : x <= y => y <= z => x <= z.
axiom [any] lt_trans    ['a] (x,y,z : 'a) : x < y  => y < z  => x < z.
axiom [any] lt_le_trans ['a] (x,y,z : 'a) : x < y  => y <= z => x < z.
axiom [any] le_lt_trans ['a] (x,y,z : 'a) : x <= y => y < z  => x < z.

axiom [any] lt_charac ['a] (x,y : 'a) : x < y <=> (x <> y && x <= y).

axiom [any] le_not_lt_impl_eq ['a] (x,y : 'a) : x <= y => not (x < y) => x = y.

lemma [any] lt_impl_le ['a] (x,y : 'a) : x < y => x <= y.
Proof. by rewrite lt_charac. Qed.

lemma [any] not_lt_refl ['a] (x:'a) : not (x < x).
Proof. auto. Qed.

lemma [any] lt_irrefl ['a] (x : 'a) : x < x <=> false.
Proof. auto. Qed.

(* The next lemma could be strengthened as an equivalence for all
   types except timestamps. *)
axiom [any] le_impl_eq_lt ['a] (x,y : 'a) : x <= y => (x = y || x < y).

(* The ordering is not well-behaved on timestamps,
   hence some properties do not hold on all types;
   specific lemmas are given below for useful types. *)
axiom [any] le_refl_index (x:index) : x <= x.
lemma [any] le_refl_index_eq (x:index) : (x <= x) = true.
Proof.
  by rewrite le_refl_index.
Qed.
hint rewrite le_refl_index_eq.

lemma [any] le_pred_lt (t, t' : timestamp): (t <= pred(t')) = (t < t').
Proof. by rewrite eq_iff. Qed.

lemma [any] neq_le_pred_le (t, t' : timestamp):
  t<>t' => (t <= t') = (t <= pred(t')).
Proof. by rewrite eq_iff. Qed.

axiom [any] le_lt ['a] (x, x' : 'a): x <> x' => (x <= x') = (x < x').


(*------------------------------------------------------------------*)
(* lists : mem and append *)

type mset.

abstract empty_set : mset.

abstract mem : message -> mset -> bool.

abstract add : message -> mset -> mset.

axiom [any] empty_set_is_empty (x:message) : not (mem x empty_set).


 
