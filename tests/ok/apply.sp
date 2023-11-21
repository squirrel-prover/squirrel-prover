abstract a : message
abstract b : message
abstract c : message
abstract d : message
abstract e : message

name n1 : index -> message
name m1 : message
name m2 : message

abstract ok : index   -> message
abstract f  : message -> message
abstract gg : message * message -> message
abstract f0 : message -> message
channel ch

system A: !_i in(ch,x); new l; out(ch,<ok(i),<x,l>>).

system [bis] !_i in(ch,x); new l; if x = a then out(ch,<ok(i),<x,l>>).

(*------------------------------------------------------------------*)
lemma _ (x, y : message, i : index) : 
  f0(<x,y>) = ok(i) =>
  (forall (x,y : message), x = ok(i) => gg(f(x),y) = f0(x)) =>
  gg(f(f0(<x,y>)),<y,y>) = f0(f0(<x,y>)).
Proof.
  intro H Hyp.
  apply Hyp.
  assumption H.
Qed.

(* same goal, but slightly changing the conclusion to prevent application  *)
lemma _ (x, y : message, i : index) : 
  f0(<x,y>) = ok(i) =>
  (forall (x,y : message), x = ok(i) => gg(f(x),y) = f0(x)) =>
  gg(f(f0(<x,y>)),<y,y>) = f0(<x,y>).
Proof.
  intro H Hyp.
  checkfail (by apply Hyp) exn ApplyMatchFailure.
Abort.

(* all variables of the lemma are not bound by the lemma application  *)
lemma _ (x, y : message, i : index) : 
  f0(<x,y>) = ok(i) =>
  (forall (x,y : message, i : index), x = ok(i) => gg(f(x),y) = f0(x)) =>
  gg(f(f0(<x,y>)),<y,y>) = f0(<x,y>).
Proof.
  intro H Hyp.
  checkfail (apply Hyp) exn ApplyBadInst.
Abort.

(*------------------------------------------------------------------*)
(* Test `apply ... in ...`  *)
lemma _ (A,B,C,D : boolean, y : message, j : index) : 
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

axiom mtrans (x,y,z : T) : x -- y => y -- z => x -- z.

axiom mrefl (x : T) : x -- x.
axiom sym (x,y : T) : x -- y => y -- x.

lemma _ (x,y,z,w : T) : x -- y => y -- z => z -- w => x -- w.
Proof.
  intro _ _ _.
  apply mtrans _ y _.
  assumption.
  apply mtrans _ z _.
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

lemma mult_left (x,y,z : G) : x = y => z ** x = z ** y.
Proof. auto. Qed.


lemma integre (a,b,c : G) : a ** b = a ** c => b = c.
Proof.
 intro H.
 apply mult_left _ _ (inv (a)) in H.
 rewrite !-assoc !inv !neuter in H.
 assumption.
Qed.

(*==================================================================*)
(* test global apply *)

global lemma _ (x, y : message) : equiv(x, y) -> equiv(x).
Proof. 
 intro H; apply H. 
Qed.

global lemma _ (x, y : message) : equiv(y, x) -> equiv(x).
Proof. 
 intro H; apply H. 
Qed.

global lemma _ (x, y : message) : 
  [a = b] -> ([a = b] -> equiv(y, x)) -> equiv(x).
Proof.
 intro H0 H; apply H. 
 assumption.
Qed.

global lemma _ (x, y : message) : equiv(x) -> equiv(x, y).
Proof. 
 checkfail intro H; apply H exn ApplyMatchFailure. 
Abort.

global lemma _ (x : message) :
  equiv(seq (i:index => <ok(i), x>)) ->
  equiv(seq (i:index => <ok(i), x>)).
Proof.
 intro H; apply H.
Qed.

(*------------------------------------------------------------------*)
(* matching under binders *)

(* The term `ok(j)` can be computed by the adversary for any index `j`, since
   `ok` is an abstract function. *)
global lemma _ (y : message) :
 equiv(empty) ->
 equiv(seq (j:index => <ok(j), ok(j)>)).
Proof.
  intro H; apply H.
Qed.

(* From now one, we use a name `n1` to test the matching algorithm, since it 
   cannot be deduce. *)
global lemma _ (y : message) :
 equiv(empty) ->
 equiv(seq (j:index => <n1(j), n1(j)>)).
Proof.
 checkfail (intro H; apply H) exn ApplyMatchFailure.
Abort.

global lemma _ (x : message) :
  equiv(seq (i:index => <n1(i), x>)) ->
  equiv(seq (i:index => <n1(i), x>)).
Proof. 
 intro H; apply H.
Qed.

(* with alpha-renaming *)
global lemma _ (x : message) :
  equiv(seq (i:index => <n1(i), x>)) ->
  equiv(seq (j:index => <n1(j), x>)).
Proof.
 intro H; apply H.
Qed.

(* TODO: inferance is failing there. See [Match.deduce_mem_one] *)
(* global goal _ (y : message) : *)
(*   (forall (x : message), equiv(seq (i:index -> <n1(i), x>))) -> *)
(*   equiv(seq (j:index -> <n1(j), f(y)>)). *)
(* Proof. *)
(*  intro H; apply H. *)
(* Qed. *)
 
name nj : index -> message.

(* we cannot match `x` with `nj(j)` since `j` is bound in the conclusion. *)
global lemma _ :
 (Forall (x : message), equiv(seq (i:index => <n1(i), x>))) ->
 equiv(seq (j:index => <n1(j), nj(j)>)).
Proof.
 intro H.
 checkfail (apply H) exn ApplyMatchFailure.
Abort.

(* with a sequence *)
name m : index -> message.
global lemma _ : equiv(seq(i:index =>m(i))) -> equiv(seq(k:index => m(k))).
Proof. 
 intro H; apply H.
Qed.

(* with a sequence over two indices *)
name n : index * index -> message.
global lemma _ : 
  equiv(seq(i,j:index => n(i,j))) -> equiv(seq(k,l:index => n(k,l))).
Proof. 
 intro H; apply H.
Qed.

(*------------------------------------------------------------------*)
(* apply modulo FA *)

global lemma _ (x, y : message) : equiv(x,y) -> equiv(<x, y>).
Proof.
 intro H; apply H.
Qed.

abstract n0 : message.
global lemma _ (x, y : message) : equiv(x) -> equiv(n0, y).
Proof. 
 checkfail (intro H; apply H) exn ApplyMatchFailure.
Abort.

global lemma _ (x,y,z : message) : equiv(x,z) -> equiv(<x, y>).
Proof.
 checkfail (intro H; apply H) exn ApplyMatchFailure.
Abort.

(*------------------------------------------------------------------*)
(* apply modulo FA dup *)

(* with input *)
global lemma _ (t : timestamp) : equiv(frame@t) -> equiv(input@t).
Proof.
 intro H; apply H.
Qed.

global lemma _ (t : timestamp) : equiv(frame@t) -> equiv(input@pred(pred(t))).
Proof.
 intro H; apply H.
Qed.

global lemma _ (t : timestamp) : equiv(frame@pred(t)) -> equiv(input@t).
Proof.
 intro H; apply H.
Qed.

global lemma _ (t, t' : timestamp) : equiv(frame@t) -> equiv(input@t').
Proof.
 checkfail (intro H; apply H) exn ApplyMatchFailure.
Abort.

global lemma _ (t : timestamp) : equiv(input@t) -> equiv(frame@t).
Proof.
 checkfail (intro H; apply H) exn ApplyMatchFailure.
Abort.

(*------------------------------------------------------------------*)
(* with exec *)
global lemma _ (t : timestamp) : equiv(frame@t) -> equiv(exec@t).
Proof.
 intro H; apply H.
Qed.

set showStrengthenedHyp=true.

(* cond can be deduce (hence exec), because it is trivial *)
global lemma _ (t : timestamp[const]) : 
  [happens(t)] -> equiv(frame@pred(t)) -> equiv(exec@t).
Proof.
 intro Hap H.
 case t => Eq; 
 repeat destruct Eq as [_ Eq]; 
 rewrite /*; 
 apply H. 
Qed.

system [three] !_i in(ch,x); new l; if x = l then out(ch,<ok(i),<x,l>>).

(* cond cannot be deduce in system [three], because of the new name `l` *)
global lemma [three] _ (t : timestamp) : equiv(frame@pred(t)) -> equiv(exec@t).
Proof.
 intro H.
 checkfail (apply H) exn ApplyMatchFailure.
Abort.

(*------------------------------------------------------------------*)
(* with frame *)
global lemma _ (t : timestamp) : equiv(frame@t) -> equiv(frame@t).
Proof.
 intro H; apply H.
Qed.

global lemma _ (t : timestamp) : equiv(frame@pred(t)) -> equiv(frame@t).
Proof.
 checkfail (intro H; apply H) exn ApplyMatchFailure.
Abort.

(*------------------------------------------------------------------*)
(* with pairs *)

global lemma _ : 
  equiv(<m1, m2>) -> equiv(m1, m2).
Proof.
 intro H; apply H.
Qed.

global lemma _ (i : index) : 
  equiv(n1(i), <m1, m2>) -> equiv(n1(i), m1, m2).
Proof.
 intro H; apply H.
Qed.

name m3 : message.

global lemma _ (i : index) :
  equiv(n1(i), <m1, <m2, m3>>) -> equiv(n1(i), m1, m2, m3).
Proof.
 intro H; apply H.
Qed.

(*------------------------------------------------------------------*)
(* with tuples *)

name k : message.

global lemma _ (t:timestamp) :
  equiv(frame@t,(k,k)) -> equiv(frame@t,k).
Proof.
  intro H; apply H.
Qed.

(* ========================================================= *)
global axiom myax  ['a] (x, y : 'a) : equiv(x,y) -> [x = y].
global axiom myax1 ['a] (x, y : 'a) : equiv(x,y).

global lemma _ ['a] (x,y : 'a) : [x = y]. 
Proof. 
  apply myax _ _ _. 
  have A := myax1 x y.
  assumption A.
Qed. 

(* ========================================================= *)
(* three proofs of the same goal, using an axiom mixing local and 
   global hypotheses *)

abstract p ['a] : 'a -> 'a -> bool.
abstract q ['a] : 'a -> 'a -> bool.

global axiom bar ['a] (x,y : 'a) : equiv(x,y) -> [p x y => q x y].

axiom        foo1 ['a] (x,y : 'a) : p x y.
global axiom foo2 ['a] (x,y : 'a) : equiv(x,y).

(* using `have` *)
global lemma _ ['a] (x,y : 'a[const,glob]) : [q x y].
Proof. 
  byequiv.

  have A := bar x y _ _; [1: apply foo1 | 2: apply foo2].
  assumption A.
Qed. 

(* using `apply` *)
global lemma _ ['a] (x,y : 'a[const,glob]) : [q x y].
Proof. 
  byequiv.

  apply bar x y; 1: apply foo2.
  apply foo1.
Qed. 

(* using `apply` with discharge *)
global lemma _ ['a] (x,y : 'a[const,glob]) : [q x y].
Proof. 
  byequiv.

  apply bar x y _ _; [1: apply foo1 | 2: apply foo2].
Qed. 

(* ========================================================= *)
(* `apply`, in a forward style *)
global lemma _ ['a] (x,y : 'a[const,glob]) : [p x y] -> [q x y].
Proof.
  intro H.

  have A  := %local(bar x y); 1: apply foo2. 

  checkfail apply A in H exn Failure. 
  (* Failure: cannot match a local lemma in a global hypothesis  *)
 
  localize H as H0; clear H.
  apply A in H0.
  assumption H0.
Qed.

(* `apply`, in a forward style *)
global lemma _ ['a] (x,y : 'a[const,glob]) : [p x y] -> [q x y].
Proof.
  intro H.

  have A := %local(bar x y _); 1: apply foo2.  

  checkfail apply A in H exn Failure. 
  (* Failure: cannot match a local lemma in a global hypothesis  *)
 
  localize H as H0; clear H.
  apply A in H0.
  assumption H0.
Qed.

(* `apply`, in a forward style *)
global lemma _ ['a] (x,y : 'a[const,glob]) : equiv(x,y) -> [q x y].
Proof.
  intro H.

  apply bar x y in H. 
  (have H0 := H _; 1: apply foo1); clear H.
  assumption H0.
Qed.

(* ========================================================= *)
global axiom foog t : [happens(t)] -> equiv(t).

(* `apply`, in a forward style *)
global lemma _ t : [happens(t)] -> equiv(t).
Proof.
  intro H.
  apply foog in H.
  assumption H.
Qed.
