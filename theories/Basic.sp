(*------------------------------------------------------------------*)
(* equality *)

axiom [any] eq_iff (x, y : boolean) : (x = y) = (x <=> y).

axiom [any] eq_not (x, y : boolean) : (not(x) = not(y)) = (x = y).

goal [any] eq_sym ['a] (x,y : 'a) : (x = y) = (y = x).
Proof. by rewrite eq_iff. Qed.

goal [any] neq_sym ['a] (x,y : 'a) : (x <> y) = (y <> x).
Proof. by rewrite eq_iff. Qed.

goal [any] eq_refl_e ['a] (x : 'a) : (x = x) = true.
Proof.
  by rewrite eq_iff.
Qed.
hint rewrite eq_refl_e.

goal [any] eq_refl ['a] (x : 'a) : x = x.
Proof. 
  by rewrite eq_refl_e.
Qed.

goal [any] neq_irefl ['a] (x : 'a) : (x <> x) <=> false.
Proof. by split. Qed.
hint rewrite neq_irefl.

(*------------------------------------------------------------------*)
(* true/false *)

axiom [any] true_false : (true = false) = false.
hint rewrite true_false.

goal [any] false_true : (false = true) = false.
Proof. 
  by rewrite (eq_sym false true).
Qed.
hint rewrite false_true.

goal [any] eq_true (b:boolean) : (b = true) = b.
Proof. by case b. Qed.
hint rewrite eq_true.

goal [any] eq_true2 (b:boolean) : (true = b) = b.
Proof. by case b. Qed.
hint rewrite eq_true2.

(*------------------------------------------------------------------*)
(* not *)

axiom [any] not_true : not(true) = false.
hint rewrite not_true.

axiom [any] not_false : not(false) = true.
hint rewrite not_false.


goal [any] not_not (b : boolean): not (not b) = b.
Proof.
  by case b.
Qed.
hint rewrite not_not.

goal [any] not_eq ['a] (x, y : 'a): not (x = y) = (x <> y).
Proof. 
by rewrite eq_iff. 
Qed.
hint rewrite not_eq.

goal [any] not_neq ['a] (x, y : 'a): not (x <> y) = (x = y).
Proof. 
by rewrite eq_iff. 
Qed.
hint rewrite not_neq.

goal [any] not_eqfalse (b:boolean) : (b = false) = not(b).
Proof.
 by case b.
Qed.

goal [any] not_impl (a, b:bool) : not (a => b) = (a && not b).
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

goal [any] eq_false ['a] (x, y : 'a): ((x = y) = false) = (x <> y).
Proof. 
rewrite -not_eq. case (x = y) => _. simpl. auto.
by rewrite eq_iff. 
Qed.
hint rewrite eq_false.

(*------------------------------------------------------------------*)
(* and *)

axiom [any] and_comm (b,b' : boolean) : (b && b') = (b' && b).

axiom [any] and_true_l (b : boolean) : (true && b) = b.
hint rewrite and_true_l.

goal [any] and_true_r (b : boolean) : (b && true) = b.
Proof. by rewrite and_comm and_true_l. Qed.
hint rewrite and_true_r.

axiom [any] and_false_l (b : boolean) : (false && b) = false.
hint rewrite and_false_l.

goal [any] and_false_r (b : boolean) : (b && false) = false.
Proof. by rewrite and_comm and_false_l. Qed.
hint rewrite and_false_r.

(*------------------------------------------------------------------*)
(* or *)
axiom [any] or_comm (b,b' : boolean) : (b || b') = (b' || b).

axiom [any] or_false_l (b : boolean) : (false || b) = b.
hint rewrite or_false_l.

goal [any] or_false_r (b : boolean) : (b || false) = b.
Proof. by rewrite or_comm or_false_l. Qed.
hint rewrite or_false_r.

axiom [any] or_true_l (b : boolean) : (true || b) = true.
hint rewrite or_true_l.

goal [any] or_true_r (b : boolean) : (b || true) = true.
Proof. by rewrite or_comm or_true_l. Qed.
hint rewrite or_true_r.

(*------------------------------------------------------------------*)
(* impl *)
goal [any] impl_charac (b,b' : boolean) : (b => b') = ((not b) || b').
Proof. 
  rewrite eq_iff; split; case b; case b' => //=. 
Qed.

goal [any] impl_false_l (b : boolean) : (false => b) = true.
Proof. by rewrite eq_iff; case b. Qed.
hint rewrite impl_false_l.

goal [any] impl_true_r (b : boolean) : (b => true) = true.
Proof. auto. Qed.
hint rewrite impl_true_r.

goal [any] impl_true_false : (true => false) = false.
Proof. by rewrite impl_charac. Qed.
hint rewrite impl_true_false.

(*------------------------------------------------------------------*)
(* not: more lemmas *)

goal [any] not_and (a, b : boolean): not (a && b) = (not a || not b).
Proof. 
  rewrite eq_iff. 
  case a; case b => //=.
Qed.

goal [any] not_or (a, b : boolean): not (a || b) = (not a && not b).
Proof. 
  rewrite eq_iff. 
  case a; case b => //=.
Qed.

(*------------------------------------------------------------------*)
(* if *)

goal [any] if_true ['a] (b : boolean, x,y : 'a):
 b => if b then x else y = x.
Proof.
  intro *.
  case (if b then x else y).
  + auto.
  + intro [HH _]. by use HH.
Qed.

goal [any] if_true0 ['a] (x,y : 'a):
 if true then x else y = x.
Proof.
  by rewrite if_true. 
Qed.
hint rewrite if_true0.

goal [any] if_false ['a] (b : boolean, x,y : 'a):
 (not b) => if b then x else y = y.
Proof. 
  intro *; case (if b then x else y).
  + intro [H1 H2]. 
    by rewrite H1 in H2. 
  + auto.
Qed.

goal [any] if_false0 ['a] (x,y : 'a):
 if false then x else y = y.
Proof.
  by rewrite if_false.
Qed.
hint rewrite if_false0.

goal [any] if_then_then ['a] (b,b' : boolean, x,y : 'a):
  if b then (if b' then x else y) else y = if (b && b') then x else y.
Proof.  
  by case b; case b'.
Qed.

goal [any] if_then_implies ['a] (b,b' : boolean, x,y,z : 'a):
  if b then (if b' then x else y) else z =
  if b then (if b => b' then x else y) else z.
Proof.
  case b; intro H; case b'; intro H'; simpl; try auto.  
Qed.

goal [any] if_same ['a] (b : boolean, x : 'a):
  if b then x else x = x.
Proof.
  by case b.
Qed.
hint rewrite if_same.

goal [any] if_then ['a] (b,b' : boolean, x,y,z : 'a):
 b = b' => 
 if b then (if b' then x else y) else z = 
 if b then x else z.
Proof.
  by intro ->; case b'.
Qed.
hint rewrite if_then.

goal [any] if_else ['a] (b,b' : boolean, x,y,z : 'a):
 b = b' => 
 if b then x else (if b' then y else z) = 
 if b then x else z.
Proof.
  by intro ->; case b'.
Qed.
hint rewrite if_else.

goal [any] if_then_not ['a] (b,b' : boolean, x,y,z : 'a):
 b = not b' => 
 if b then (if b' then x else y) else z = 
 if b then y else z.
Proof.
  by intro ->; case b'.
Qed.
hint rewrite if_then_not.

goal [any] if_else_not ['a] (b,b' : boolean, x,y,z : 'a):
  b = not b' => 
 if b then x else (if b' then y else z) = 
 if b then x else y.
Proof.  
  by intro ->; case b'.
Qed.
hint rewrite if_else_not.

(*------------------------------------------------------------------*)
(* some functional properties *)

goal [any] fst_pair (x,y : message) : fst (<x,y>) = x.
Proof. auto. Qed.
hint rewrite fst_pair.

goal [any] snd_pair (x,y : message) : snd (<x,y>) = y.
Proof. auto. Qed.
hint rewrite snd_pair.

(*------------------------------------------------------------------*)
(* if-and-only-if *)

goal [any] iff_def (x,y : boolean) : (x <=> y) = ((x => y) && (y => x)).
Proof. 
 rewrite eq_iff; split.
 by intro ->. 
 auto.
Qed.

goal [any] iff_refl (x : boolean) : (x <=> x) = true.
Proof.
 by rewrite eq_iff. 
Qed.
hint rewrite iff_refl.

goal [any] iff_sym (x, y: boolean) : (x <=> y) = (y <=> x).
Proof.
 by rewrite eq_iff !iff_def.
Qed.

goal [any] true_iff_false : (true <=> false) = false.
Proof.
 by rewrite -eq_iff. 
Qed.
hint rewrite true_iff_false.

goal [any] false_iff_true : (false <=> true) = false.
Proof.
 by rewrite -eq_iff. 
Qed.
hint rewrite false_iff_true.




(*------------------------------------------------------------------*)
(* exists *)

goal [any] exists_false1 ['a]:
(exists (a:'a), false) = false.
Proof. by rewrite not_eqfalse. Qed.

goal [any] exists_false2 ['a 'b]:
(exists (a:'a, b:'b), false) = false.
Proof. by rewrite not_eqfalse. Qed.

goal [any] exists_false3 ['a 'b 'c]:
(exists (a:'a, b:'b, c:'c), false) = false.
Proof. by rewrite not_eqfalse. Qed.

goal [any] exists_false4 ['a 'b 'c 'd]:
(exists (a:'a, b:'b, c:'c, d:'d), false) = false.
Proof. by rewrite not_eqfalse. Qed.

goal [any] exists_false5 ['a 'b 'c 'd 'e]:
(exists (a:'a, b:'b, c:'c, d:'d, e:'e), false) = false.
Proof. by rewrite not_eqfalse. Qed.

goal [any] exists_false6 ['a 'b 'c 'd 'e 'f]:
(exists (a:'a, b:'b, c:'c, d:'d, e:'e, f:'f), false) = false.
Proof. by rewrite not_eqfalse. Qed.



(*------------------------------------------------------------------*)
(* forall *)


goal [any] forall_true1 ['a]:
(forall (a:'a), true) = true.
Proof. auto. Qed.

goal [any] forall_true2 ['a 'b]:
(forall (a:'a, b:'b), true) = true.
Proof. auto. Qed.

goal [any] forall_true3 ['a 'b 'c]:
(forall (a:'a, b:'b, c:'c), true) = true.
Proof. auto. Qed.

goal [any] forall_true4 ['a 'b 'c 'd]:
(forall (a:'a, b:'b, c:'c, d:'d), true) = true.
Proof. auto. Qed.

goal [any] forall_true5 ['a 'b 'c 'd 'e]:
(forall (a:'a, b:'b, c:'c, d:'d, e:'e), true) = true.
Proof. auto. Qed.

goal [any] forall_true6 ['a 'b 'c 'd 'e 'f]:
(forall (a:'a, b:'b, c:'c, d:'d, e:'e, f:'f), true) = true.
Proof. auto. Qed.


(*------------------------------------------------------------------*)
(* length *)

axiom [any] len_zeroes (x:message) : len(zeroes(x)) = len(x).
hint rewrite len_zeroes.


(*------------------------------------------------------------------*)
(* exec and cond *)

(* Squirrel can only expand exec for specific actions.
   This action allows to go beyond this. It would be provable
   in any system, by performing a case analysis on tau. *)
axiom [any] exec_not_init (tau:timestamp) :
  init < tau => exec@tau = (exec@pred(tau) && cond@tau).

axiom [any] exec_init (tau:timestamp) : tau = init => exec@tau = true.
axiom [any] cond_init (tau:timestamp) : tau = init => cond@tau = true.

goal [any] exec_le (tau,tau':timestamp) : tau' <= tau => exec@tau => exec@tau'.
Proof.
  induction tau => tau IH Hle Hexec.
  case (tau = tau').
  + auto.
  + intro Hneq.
    rewrite exec_not_init // in Hexec.
    by apply IH (pred(tau)).
Qed.

goal [any] exec_cond (tau:timestamp) : happens(tau) => exec@tau => cond@tau.
Proof.
  intro Hap Hexec.
  case (init < tau) => _.
  - by rewrite exec_not_init in Hexec.
  - by rewrite cond_init.
Qed.

(*------------------------------------------------------------------*)

goal [any] f_apply ['a 'b] (f : 'a -> 'b) (x, y : 'a) : x = y => f x = f y.
Proof. by intro ->. Qed.

goal [any] not_exists_1 ['a] (phi:'a -> bool) :
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

goal [any] not_exists_2 ['a 'b] (phi:'a -> 'b -> bool) :
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
