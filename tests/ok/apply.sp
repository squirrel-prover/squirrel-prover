set autoIntro=false.

abstract a : message
abstract b : message
abstract c : message
abstract d : message
abstract e : message

abstract ok : index   -> message
abstract f  : message -> message
abstract gg  : message -> message -> message
abstract f0  : message -> message
channel ch

system A: !_i in(ch,x);out(ch,<ok(i),x>).

system [bis] !_i in(ch,x);if x = a then out(ch,<ok(i),x>).

goal _ (x, y : message, i : index) : 
  f0(<x,y>) = ok(i) =>
  (forall (x,y : message), x = ok(i) => gg(f(x),y) = f0(x)) =>
  gg(f(f0(<x,y>)),<y,y>) = f0(f0(<x,y>)).
Proof.
  intro H Hyp.
  apply Hyp.
  assumption.
Qed.

(* same goal, but slightly changing the conclusion to prevent application  *)
goal _ (x, y : message, i : index) : 
  f0(<x,y>) = ok(i) =>
  (forall (x,y : message), x = ok(i) => gg(f(x),y) = f0(x)) =>
  gg(f(f0(<x,y>)),<y,y>) = f0(<x,y>).
Proof.
  intro H Hyp.
  checkfail (apply Hyp) exn ApplyMatchFailure.
Abort.

(* all variables of the lemma are not bound by the lemma application  *)
goal _ (x, y : message, i : index) : 
  f0(<x,y>) = ok(i) =>
  (forall (x,y : message, i : index), x = ok(i) => gg(f(x),y) = f0(x)) =>
  gg(f(f0(<x,y>)),<y,y>) = f0(<x,y>).
Proof.
  intro H Hyp.
  checkfail (apply Hyp) exn ApplyBadInst.
Abort.

(*------------------------------------------------------------------*)
(* Test `apply ... in ...`  *)
goal _ (A,B,C,D : boolean, y : message, j : index) : 
  A => B => C => (D => False) =>
  (forall (x : message, i : index), A => x = ok(i) => B => D) =>
  (C => f(y) = ok(j)) => False.
Proof.
  intro Ha Hb Hc Hfinal H Hin.
  apply H in Hin;
  [1,2,3: assumption |
   4: by apply Hfinal]. 
Qed.

(*==================================================================*)
(* test apply with patterns *)

(*------------------------------------------------------------------*)
(* transitivity *)
type T.
abstract ( -- ) : T -> T -> boolean.

axiom trans (x,y,z : T) : x -- y => y -- z => x -- z.

axiom mrefl (x : T) : x -- x.
axiom sym (x,y : T) : x -- y => y -- x.

goal _ (x,y,z,w : T) : x -- y => y -- z => z -- w => x -- w.
Proof.
  intro _ _ _.
  apply trans _ y _.
  assumption.
  apply trans _ z _.
  assumption.
  assumption.
Qed.

(*------------------------------------------------------------------*)
(* small group axioms *)

type G.

abstract ( ** ) : G -> G -> G.

abstract inv : G -> G.
abstract ge : G.

axiom inv (x : G) : inv (x) ** x = ge.
axiom comm (x, y : G) : x ** y = y ** x.
axiom assoc (x,y,z : G) : (x ** y) ** z = x ** (y ** z).
axiom neuter (x : G) : ge ** x = x.

goal mult_left (x,y,z : G) : x = y => z ** x = z ** y.
Proof. auto. Qed.


goal integre (a,b,c : G) : a ** b = a ** c => b = c.
Proof.
 intro H.
 apply mult_left _ _ (inv (a)) in H.
 rewrite !-assoc !inv !neuter in H.
 assumption.
Qed.

(*==================================================================*)
(* test equiv apply *)

equiv _ (x, y : message) : x, y -> x.
Proof. 
 intro H; apply H. 
Qed.

equiv _ (x, y : message) : y, x -> x.
Proof. 
 intro H; apply H. 
Qed.

(* equiv _ (x, y : message) : [a = b] -> ([a = b] -> y, x) -> x. *)
(* Proof. *)
(*  intro H0 H; apply H; assumption. *)
(* Qed. *)

equiv _ (x, y : message) : x -> x, y.
Proof. 
 checkfail intro H; try apply H; auto exn GoalNotClosed. 
Abort.

equiv _ (x : message) : seq (i -> <ok(i), x>) -> seq (i -> <ok(i), x>).
Proof. 
 intro H; apply H.
Qed.

(*------------------------------------------------------------------*)
(* matching under binders *)

equiv _ (x : message) : seq (i -> <ok(i), x>) -> seq (i -> <ok(i), x>).
Proof. 
 intro H; apply H.
Qed.

(* with alpha-renaming *)
equiv _ (x : message) : seq (i -> <ok(i), x>) -> seq (j -> <ok(j), x>).
Proof. 
 intro H; apply H.
Qed.

(* TODO: commented out as we cannot (yet) parse general equivalence formulas. *)
(* equiv _ (y : message) :  *)
(*   (forall (x : message), seq (i -> <ok(i), x>)) -> seq (j -> <ok(j), f(y)>). *)
(* Proof.  *)
(*  intro H; apply H. *)
(* Qed. *)

(* equiv _ (y : message) :  *)
(*   (forall (x : message), seq (i -> <ok(i), x>)) -> seq (j -> <ok(j), ok(i)>). *)
(* Proof.  *)
(*  checkfail intro H; try by apply H exn GoalNotClosed. *)
(* Abort. *)

(* with a sequence *)
name m : index -> message.
equiv _ : seq(i->m(i)) -> seq(k->m(k)).
Proof. 
 intro H; apply H.
Qed.

(* with a sequence over two indices *)
name n : index -> index -> message.
equiv _ : seq(i,j->n(i,j)) -> seq(k,l->n(k,l)).
Proof. 
 intro H; apply H.
Qed.

(*------------------------------------------------------------------*)
(* apply modulo FA *)

equiv _ (x, y : message) : x,y -> <x, y>.
Proof.
 intro H; apply H.
Qed.

abstract n0 : message.
equiv _ (x, y : message) : x -> n0, y.
Proof. 
 checkfail (intro H; by try apply H) exn GoalNotClosed.
Abort.

equiv _ (x,y,z : message) : x,z -> <x, y>.
Proof.
 checkfail (intro H; by try apply H) exn GoalNotClosed.
Abort.
