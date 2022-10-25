

abstract a : message
abstract b : message
abstract c : message
abstract d : message
abstract e : message

abstract ok : index   -> message
abstract f  : message -> message
abstract gg  : message * message -> message
abstract f0  : message -> message
channel ch

system A: !_i in(ch,x);out(ch,<ok(i),x>).

system [bis] !_i in(ch,x);if x = a then out(ch,<ok(i),x>).

include Basic.

axiom foo (x : message) : f(x) = a.
axiom foog (x : message) : gg(x,b) = c.

(*------------------------------------------------------------------*)
(* rewrite all instances of only the first occurrence found. *)
goal _ (x, y, z : message) :
  (a = z && a = y && (f(z) = z || z = y)) =>
  (f(x) = z && f(x) = y && (f(z) = z || z = y)).
Proof.
  intro H. 
  rewrite foo.
  assumption.
Qed.

(* rewrite the first occurrence found. *)
goal _ (x, y, z : message) : 
(a = z && f(z) = y && (f(z) = z || z = y)) =>
(f(x) = z && f(z) = y && (f(z) = z || z = y)).
Proof.
  intro H.
  rewrite foo.
  assumption.
Qed.

goal foo_lem (x : message) : f(x) = a.
Proof. 
  by use foo with x.
Qed.

(* same but through an already proved goal. *)
goal _ (x, y, z : message) : 
(a = z && f(z) = y && (f(z) = z || z = y)) =>
(f(x) = z && f(z) = y && (f(z) = z || z = y)).
Proof.
  intro H.
  rewrite foo_lem.
  assumption.
Qed.

(* same, but through an hypothesis (we changed `a` into `b` to check that
   hypotheses have priority over lemmas and axioms). *)
goal _ (x, y, z : message) : 
(forall (x : message), f(x) = d) =>
(d = z && f(z) = y && (f(z) = z || z = y)) =>
(f(x) = z && f(z) = y && (f(z) = z || z = y)).
Proof.
  intro foo H.
  rewrite foo.
  assumption.
Qed.

(* same goal as above, by with a premise obtained from the conclusion by
   rewriting the second occurrence (hence it should fail).*)
goal _ (x, y, z : message) : 
((f(x) = z && f(x) = y) && (a = z || z = y)) =>
(f(x) = z && f(x) = y && (f(z) = z || z = y)).
Proof.
  intro H.
  rewrite foo.
  checkfail assumption exn NotHypothesis.
Abort.

(*------------------------------------------------------------------*)
(* can rewrite all instances using ! *)
goal _ (x, y, z : message) : 
(a = z && a = y && (a = z || z = y)) =>
(f(x) = z && f(x) = y && (f(z) = z || z = y)).
Proof.
  intro H.
  rewrite !foo.
  assumption.
Qed.

(* can also rewrite all instances using ? (including zero instances) *)
goal _ (x, y, z : message) : 
(a = z && a = y && (a = z || z = y)) =>
(f(x) = z && f(x) = y && (f(z) = z || z = y)).
Proof.
  intro H.
  rewrite ?foo.
  assumption.
Qed.

(*------------------------------------------------------------------*)
(* new goal using `g` and `foog` *)
goal _ (x, y, z : message) : 
(c = z && c = y && (c = z || z = y)) =>
(gg(x,b) = z && gg(x,b) = y && (gg(z,b) = z || z = y)).
Proof.
  intro H.
  rewrite ?foog.
  assumption.
Qed.

(* rewrite fails if no instances to rewrite *)
goal _ (x, y, z : message) : 
(gg(x,c) = z && gg(x,c) = y && (gg(z,c) = z || z = y)).
Proof. 
  checkfail rewrite foog exn NothingToRewrite.
Abort.

(* ! fails if no instances to rewrite *)
goal _ (x, y, z : message) : 
(gg(x,c) = z && gg(x,c) = y && (gg(z,c) = z || z = y)).
Proof.
  checkfail rewrite !foog exn NothingToRewrite.
Abort.

(* ? does not fails if no instances to rewrite *)
goal _ (x, y, z : message) : 
(gg(x,c) = z && gg(x,c) = y && (gg(z,c) = z || z = y)) =>
(gg(x,c) = z && gg(x,c) = y && (gg(z,c) = z || z = y)).
Proof.
  intro H.
  rewrite ?foog.
  assumption.
Qed.

(*------------------------------------------------------------------*)
(* can rewrite in the other direction *)
goal _ (x, y, z : message) : 
a = b => c = d =>
(gg(b,b) = gg(b,b) && gg(c,c) = gg(c,c)) =>
(gg(a,a) = gg(a,b) && gg(d,c) = gg(c,c)).
Proof.
  intro AB CD H.
  rewrite !AB.
  rewrite -CD.
  assumption.
Qed.

(* same goal, but proved chaining rewrites. *)
goal _ (x, y, z : message) : 
a = b => c = d =>
(gg(b,b) = gg(b,b) && gg(c,c) = gg(c,c)) =>
(gg(a,a) = gg(a,b) && gg(d,c) = gg(c,c)).
Proof.
  intro AB CD H.
  rewrite !AB -CD.
  assumption.
Qed.

(* set debugTactics=true. *)

(*------------------------------------------------------------------*)
(* cannot rewrite if all rhs variables are not bound by the lhs *)
(* same goal, but proved chaining rewrites. *)
axiom fooA (t : message) : f(a) = t.

goal _ (x, y, z : message) : 
f(a) = b.
Proof.
  checkfail rewrite fooA exn BadRewriteRule.
Abort.


(*------------------------------------------------------------------*)
goal [bis] _ (x, y, z : message, i : index) :
(input@A(i) = a => f(a) = c) =>
 happens(A(i)) => b = c => cond@A(i) => f(a) = b.
Proof.
  intro Ass Hap H1. 
  rewrite /cond H1. 
  assumption.
Qed.

system [terce] 
 !_i
   in(ch,x);
   let t = <a,x> in 
   let t' = <t,t> in
   if x = a then out(ch,t').

(*------------------------------------------------------------------*)
goal [terce] _ (x : message, i : index) :
(* (input@A(i) = a => f(a) = c) => *)
 happens(A(i)) => x = input@A(i) => output@A(i) = <<a,x>,<a,x>>.
Proof.
  intro Hap Eq. 
  rewrite /output /t' /t Eq; congruence.
Qed.

(*------------------------------------------------------------------*)
(* rewrite rule with premisses *)
goal _ (x : message) : 
 (forall (u,v : message), u = f(a) => <u,v> = <b,v>) =>
 x = f(a) => 
 <x,c> = <b,c>.
Proof.
 intro H Eq.
 rewrite H; 1: assumption. 
 congruence.
Qed.

(* several occurences *)
goal _ (x : message) : 
 (forall (u,v : message), u = f(a) => <f0(u),v> = <b,v>) =>
 x = f(a) => 
 f(x) = f(a) => 
 <f0(x),<f0(f(x)),c>> = <b,<b,c>>.
Proof.
 intro H Eq Eq2.
 rewrite H; 1: assumption. 
 rewrite H; 1: assumption.
 congruence.
Qed.

(* same with !H *)
goal _ (x : message) : 
 (forall (u,v : message), u = f(a) => <f0(u),v> = <b,v>) =>
 x = f(a) => 
 f(x) = f(a) => 
 <f0(x),<f0(f(x)),c>> = <b,<b,c>>.
Proof.
 intro H Eq Eq2.
 rewrite !H; 1,2: assumption. 
 congruence.
Qed.

(*------------------------------------------------------------------*)

axiom mif_true ['a] (b : boolean, x,y : 'a):
 b => if b then x else y = x.

axiom mif_false ['a] (b : boolean, x,y : 'a):
 (not b) => if b then x else y = y.

goal _ (b,b' : boolean, x,y : message) : 
  b => b' => if (b && b') then x else y = x.
Proof.
 intro Hb Hb'.
 by rewrite mif_true. 
Qed.

(* same with an type variable *)
goal _ ['a] (b,b' : boolean, x,y : 'a) : 
  b => b' => if (b && b') then x else y = x.
Proof.
 intro Hb Hb'.
 by rewrite mif_true. 
Qed.

(* rewriting not at the root. *)
goal _ ['a] (b,b' : boolean, x,y : 'a) : 
  b => ((if b then x else y = x) || False).
Proof.
 intro Hb.
 by rewrite mif_true.
Qed.

(* check simplification item /= *)
goal _ (b,b' : boolean, x,y : message) : 
  b => b' => if (b && b') then x else y = x.
Proof.
 intro Hb Hb'.
 rewrite mif_true /=.

 (* /= does not close goals, hence there should be two subgoals *)
 admit.
 admit.
Qed.

(* check simplification item // *)
goal _ (b,b' : boolean, x,y : message) : 
  b => b' => if (b && b') then x else y = x.
Proof.
 intro Hb Hb'.
 rewrite mif_true //.
Qed.

(*------------------------------------------------------------------*)
(* rewriting under bindings *)

abstract p : message -> boolean.
abstract pi : index -> boolean.

goal _ (z : message) :
  (forall (u : message), p (u)) =>
  (forall (i : index), pi (i)) =>
  (exists (j : message),
    (forall (x : message), p(x) => f0(x) = j) &&
    (forall (i : index), pi(i) => ok(i) = j) &&
    < j, j > = z) =>
  forall (x : message, i : index), <f0(x), ok(i)> = z.
Proof.
  intro HP HPi [j [H1 H2 H3]].
  rewrite H1; 1: by intro _; apply HP.
  rewrite H2; 1: by intro _; apply HPi.
  rewrite H3.
  intro _ _; congruence.
Qed.

(*------------------------------------------------------------------*)
(* rewriting with pattern holes *)

abstract P : message * message -> boolean.

goal _ (z : message) :
  (forall (x,y : message), P(x,y) => f(y) = x) =>
   P(a, z) => <f(z),b> = <a, b>.
Proof.
  intro H Assum.
  rewrite (H a _).
  assumption.
  congruence.
Qed.

(* same but we also give a (useless) pattern hole *)
goal _ (z : message) :
  (forall (x,y : message), P(x,y) => f(y) = x) =>
   P(a, z) => <f(z),b> = <a, b>.
Proof.
  intro H Assum.
  rewrite (H a _).
  assumption.
  congruence.
Qed.

(*------------------------------------------------------------------*)
(* rewriting frame elements *)

axiom diff_ax ['a] (x : 'a) : diff(x,x) = x.

global goal _ (x,y,z : message) : 
  equiv(x, z) ->
  [forall (x,y : message), f(<x,y>) = x] ->
  equiv(diff(f(<x,y>),x), x, diff(f(<z,z>), z)).
Proof.
  intro Hx H.
  rewrite H diff_ax in 0,2. 
  apply Hx.
Qed.

(* same renaming variables *)
global goal _ (u,v,z : message) : 
  equiv(u, z) ->
  [forall (x,y : message), f(<x,y>) = x] ->
  equiv(diff(f(<u,v>),u), u, diff(f(<z,z>), z)).
Proof.
  intro Hx H.
  rewrite H diff_ax in 0,2. 
  apply Hx.
Qed.

(* same with variable conflict *)
global goal _ (x,v,z : message) : 
  equiv(x, z) ->
  [forall (x,y : message), f(<x,y>) = x] ->
  equiv(diff(f(<x,v>),x), x, diff(f(<z,z>), z)).
Proof.
  intro Hx H.
  rewrite H diff_ax in 0,2. 
  apply Hx.
Qed.

global goal _ (x : message) : 
  [forall (x,y : message), f(<x,y>) = x] ->
  equiv(x).
Proof.
  intro H.
  checkfail try(rewrite H in 0); auto exn GoalNotClosed.
Abort.


global goal _ (x : message) : 
  [forall (x,y : message), f(<x,y>) = x] ->
  equiv(x).
Proof.
  intro H.
  checkfail try(rewrite H in 1); auto exn GoalNotClosed.
Abort.

global goal _ (x : message) : 
  [forall (x,y : message), f(<x,y>) = x] ->
  equiv(x).
Proof.
  intro H.
  checkfail try(rewrite H in 0,1); auto exn GoalNotClosed.
Abort.


global goal _ (x,y,z : message) :
  equiv(x, y) ->
  [forall (x,y : message), f(<x,y>) = x] ->
  equiv(f(<x,f(z)>), y).
Proof. 
  intro Hx H.
  rewrite H.
  apply Hx.
Qed.

(*------------------------------------------------------------------*)
(* test failures when rewriting in global formulas *)

(* rewrite fails if no instances to rewrite *)
global goal _ (x, y, z : message) : 
[gg(x,c) = z && gg(x,c) = y && (gg(z,c) = z || z = y)].
Proof. 
  checkfail rewrite foog exn NothingToRewrite.
Abort.

(* idem with an equiv *)
global goal _ (x, y, z : message) : 
equiv(x, gg(x,c)).
Proof. 
  checkfail rewrite foog exn NothingToRewrite.
Abort.

(* ! fails if no instances to rewrite *)
global goal _ (x, y, z : message) : 
[gg(x,c) = z && gg(x,c) = y && (gg(z,c) = z || z = y)].
Proof.
  checkfail rewrite !foog exn NothingToRewrite.
Abort.

(* idem with an equiv *)
global goal _ (x, y, z : message) : 
equiv(x, gg(x,c)).
Proof. 
  checkfail rewrite !foog exn NothingToRewrite.
Abort.

(* ? does not fails if no instances to rewrite *)
global goal _ (x, y, z : message) : 
[gg(x,c) = z && gg(x,c) = y && (gg(z,c) = z || z = y)] ->
[gg(x,c) = z && gg(x,c) = y && (gg(z,c) = z || z = y)].
Proof.
  intro H.
  rewrite ?foog.
  assumption.
Qed.

(* idem with an equiv *)
global goal _ (x, y, z : message) : 
equiv(x, gg(x,c)) -> equiv(gg(x,c)).
Proof. 
  intro H.
  rewrite ?foog.
  assumption.
Qed.

(*------------------------------------------------------------------*)
goal _ : (<f(a),b> = c) => (a = f(a)) => <a,b> = c.
Proof.
  intro H ->.
  assumption.
Qed.

(*------------------------------------------------------------------*)
(* test type infer in matching *)

goal [any] _ : (exists (i : index), false) = false.
Proof. by rewrite exists_false1. Qed.

goal [any] _ : (exists (i : message), false) = false.
Proof. by rewrite exists_false1. Qed.

goal [any] _ : (exists (i : timestamp), false) = false.
Proof. by rewrite exists_false1. Qed.

goal [any] _ ['a] : (exists (i : 'a), false) = false.
Proof. by rewrite exists_false1. Qed.

(*------------------------------------------------------------------*)
(* check that `rewrite` exploits conditions when rewriting *)

goal [any] _ (b : boolean, x, y, z : message) : 
  (b => x = y) => if b then x else z = if b then y else z.
Proof.
  intro H.
  by rewrite H.
Qed.

goal [any] _ (b : boolean, x, y, z : message) : 
  (not b => z = y) => if b then x else z = if b then x else y.
Proof.
  intro H.
  rewrite H //. 
Qed.

(*------------------------------------------------------------------*)
(* rewrite n times *)

goal [any] _ ['a] (f : 'a -> 'a, a,b,c,d,z : 'a, y : 'a) : 
  (forall (x : 'a), f x = y) => 
  (f a = z) =>
  (f b = z) => 
  (f c = z) =>
  (f d = z) =>
  (f a,f b,f c,f d) = (y,z,z,z) &&
  (f a,f b,f c,f d) = (y,y,z,z) &&
  (f a,f b,f c,f d) = (y,y,y,z) &&
  (f a,f b,f c,f d) = (z,z,z,z).
Proof.
  intro H Ha Hb Hc Hd.
  split; 2: split; 2:split.
  + checkfail rewrite !H Hb Hc Hd; apply eq_refl exn NothingToRewrite.
    rewrite H Hb Hc Hd; apply eq_refl.
  + checkfail rewrite 2!H Hb Hc Hd; apply eq_refl exn NothingToRewrite.
    rewrite 2!H Hc Hd; apply eq_refl.
  + rewrite 3!H Hd; apply eq_refl.
  + rewrite 0!H Ha Hb Hc Hd; apply eq_refl.
Qed.

(*------------------------------------------------------------------*)
(* rewrite a negation *)

goal _ ['a] (x, y : 'a, p,q : bool) : not (x = y) => ((x = y) || p) => (false || p).
Proof.
  intro H H1.
  checkfail (assumption H1) exn NotHypothesis.
  rewrite H in H1.
  assumption H1.
Qed.
