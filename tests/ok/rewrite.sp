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

axiom foo : forall (x : message), f(x) = a.
axiom foog : forall (x : message), gg(x,b) = c.

(*------------------------------------------------------------------*)
(* rewrite all instances of only the first occurrence found. *)
goal _ (x, y, z : message) : 
((a = z && a = y) && (f(z) = z || z = y)) =>
(f(x) = z && f(x) = y && (f(z) = z || z = y)).
Proof.
  intro x y z H.
  rewrite (forall (x : message), f(x) = a);
  1: by intro x1; use foo with x1.
  assumption.
Qed.

(* same but directly using the axiom. *)
goal _ (x, y, z : message) : 
((a = z && a = y) && (f(z) = z || z = y)) =>
(f(x) = z && f(x) = y && (f(z) = z || z = y)).
Proof.
  intro x y z H.
  rewrite foo.
  assumption.
Qed.

goal foo_lem (x : message) : f(x) = a.
Proof. 
  by intro x; by use foo with x.
Qed.

(* same but through an already proved goal. *)
goal _ (x, y, z : message) : 
((a = z && a = y) && (f(z) = z || z = y)) =>
(f(x) = z && f(x) = y && (f(z) = z || z = y)).
Proof.
  intro x y z H.
  rewrite foo_lem.
  assumption.
Qed.

(* same, but through an hypothesis (we changed `a` into `b` to check that
   hypotheses have priority over lemmas and axioms). *)
goal _ (x, y, z : message) : 
(forall (x : message), f(x) = d) =>
((d = z && d = y) && (f(z) = z || z = y)) =>
(f(x) = z && f(x) = y && (f(z) = z || z = y)).
Proof.
  intro x y z foo H.
  rewrite foo.
  assumption.
Qed.

(* same goal as above, by with a premise obtained from the conclusion by
   rewriting the second occurrence (hence it should fail).*)
goal _ (x, y, z : message) : 
((f(x) = z && f(x) = y) && (a = z || z = y)) =>
(f(x) = z && f(x) = y && (f(z) = z || z = y)).
Proof.
  intro x y z H.
  rewrite foo.
  checkfail assumption exn NotHypothesis.
Abort.

(*------------------------------------------------------------------*)
(* can rewrite all instances using ! *)
goal _ (x, y, z : message) : 
((a = z && a = y) && (a = z || z = y)) =>
(f(x) = z && f(x) = y && (f(z) = z || z = y)).
Proof.
  intro x y z H.
  rewrite !foo.
  assumption.
Qed.

(* can also rewrite all instances using ? (including zero instances) *)
goal _ (x, y, z : message) : 
((a = z && a = y) && (a = z || z = y)) =>
(f(x) = z && f(x) = y && (f(z) = z || z = y)).
Proof.
  intro x y z H.
  rewrite ?foo.
  assumption.
Qed.

(*------------------------------------------------------------------*)
(* new goal using `g` and `foog` *)
goal _ (x, y, z : message) : 
((c = z && c = y) && (c = z || z = y)) =>
(gg(x,b) = z && gg(x,b) = y && (gg(z,b) = z || z = y)).
Proof.
  intro x y z H.
  rewrite ?foog.
  assumption.
Qed.

(* rewrite fails if no instances to rewrite *)
goal _ (x, y, z : message) : 
(gg(x,c) = z && gg(x,c) = y && (gg(z,c) = z || z = y)).
Proof.
  intro x y z.  
  checkfail rewrite foog exn NothingToRewrite.
Abort.

(* ! fails if no instances to rewrite *)
goal _ (x, y, z : message) : 
(gg(x,c) = z && gg(x,c) = y && (gg(z,c) = z || z = y)).
Proof.
  intro x y z.  
  checkfail rewrite !foog exn NothingToRewrite.
Abort.

(* ? does not fails if no instances to rewrite *)
goal _ (x, y, z : message) : 
(gg(x,c) = z && gg(x,c) = y && (gg(z,c) = z || z = y)) =>
(gg(x,c) = z && gg(x,c) = y && (gg(z,c) = z || z = y)).
Proof.
  intro x y z H.
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
  intro x y z AB CD H.
  rewrite AB.
  rewrite -CD.
  assumption.
Qed.

(* same goal, but proved chaining rewrites. *)
goal _ (x, y, z : message) : 
a = b => c = d =>
(gg(b,b) = gg(b,b) && gg(c,c) = gg(c,c)) =>
(gg(a,a) = gg(a,b) && gg(d,c) = gg(c,c)).
Proof.
  intro x y z AB CD H.
  rewrite AB -CD.
  assumption.
Qed.

(* set debugTactics=true. *)

(*------------------------------------------------------------------*)
(* cannot rewrite if all rhs variables are not bound by the lhs *)
(* same goal, but proved chaining rewrites. *)
goal _ (x, y, z : message) : 
f(a) = b.
Proof.
  intro x y z.
  checkfail rewrite (forall (t : message), f(a) = t) exn BadRewriteRule.
Abort.


(*------------------------------------------------------------------*)
goal [none, bis] _ (x, y, z : message, i : index) :
(input@A(i) = a => f(a) = c) =>
 happens(A(i)) => b = c => cond@A(i) => f(a) = b.
Proof.
  intro x y z i Ass Hap H1. 
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
goal [none, terce] _ (x : message, i : index) :
(* (input@A(i) = a => f(a) = c) => *)
 happens(A(i)) => x = input@A(i) => output@A(i) = <<a,x>,<a,x>>.
Proof.
  intro x i Hap Eq. 
  rewrite /output /t' /t Eq; congruence.
Qed.

(*------------------------------------------------------------------*)
(* rewrite rule with premisses *)
goal _ (x : message) : 
 (forall (u,v : message), u = f(a) => <u,v> = <b,v>) =>
 x = f(a) => 
 <x,c> = <b,c>.
Proof.
 intro x H Eq.
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
 intro x H Eq Eq2.
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
 intro x H Eq Eq2.
 rewrite !H; 1,2: assumption. 
 congruence.
Qed.

(*------------------------------------------------------------------*)

axiom mif_true : 
 forall (b : boolean, x,y : message),
 b => if b then x else y = x.

axiom mif_false : 
 forall (b : boolean, x,y : message),
 (not b) => if b then x else y = y.

goal _ (b,b' : boolean, x,y : message) : 
  b => b' => if (b && b') then x else y = x.
Proof.
 intro b b' x y Hb Hb'.
 by rewrite mif_true. 
Qed.

(* check simplification item /= *)
goal _ (b,b' : boolean, x,y : message) : 
  b => b' => if (b && b') then x else y = x.
Proof.
 intro b b' x y Hb Hb'.
 rewrite mif_true /=.

 (* /= does not close goals, hence there should be two subgoals *)
 admit.
 admit.
Qed.

(* check simplification item // *)
goal _ (b,b' : boolean, x,y : message) : 
  b => b' => if (b && b') then x else y = x.
Proof.
 intro b b' x y Hb Hb'.
 rewrite mif_true //.
Qed.
