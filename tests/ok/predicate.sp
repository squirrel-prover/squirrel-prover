system null.

(* --------------------------------------------------------- *)
predicate Bar {}.

global axiom bar : Bar.

(* test `apply`, `have` and `assumption` *)

global lemma _  : Bar.
Proof.
  ghave A : Bar by admit.
  apply A.
Qed.

global lemma _  : Bar.
Proof.
  apply bar.
Qed.

global lemma _  : Bar.
Proof.
  ghave A : Bar by admit.
  assumption A.
Qed.

global lemma _  : Bar.
Proof. 
  have A := bar.
  assumption A.
Qed.

(* --------------------------------------------------------- *)
predicate Bar1 {}.

global axiom bar1 : Bar1.

(* negative checks for `have` and `apply` *)

global lemma _  : Bar1.
Proof.
  ghave A : Bar by admit.
  checkfail apply A exn ApplyMatchFailure.
Abort.

global lemma _  : Bar1.
Proof.
  ghave A : Bar by admit.
  checkfail assumption A exn NotHypothesis.
Abort.

(* --------------------------------------------------------- *)
predicate Foo ['a] {} (x : 'a) y z = [x = y && y = z].

global axiom foo1 ['a] (x,y,z : 'a) : Foo x y z.
global axiom foo2                   : Foo empty empty empty.

global lemma _ ['a] (x,y,z : 'a) : [false]. 
Proof. 
  ghave ? : Foo x y z.
  ghave ? : Foo empty empty empty.
Abort.

global lemma _ ['a] (x,y,z : 'a) : Foo x y z.
Proof.
  ghave -> : [x = y] by admit.
  ghave -> : [z = y] by admit.
  ghave A  : Foo y y y by admit.
  assumption A.
Qed.

global lemma _ ['a] (x,y,z : 'a) : Foo x y z.
Proof.
  have X  : x = y by admit.
  have X' : z = y by admit.
  rewrite X X'.
  ghave A : Foo y y y by admit.
  assumption A.
Qed.

global lemma _ ['a] (x,y,z : 'a) : Foo x y z.
Proof.
  have A := foo1 x y z.
  assumption A.
Qed.

global lemma _ ['a] (x,y,z : 'a) : Foo x y z.
Proof.
  have A0 := foo1 x.
  have A  := A0 y z.
  assumption A.
Qed.

global lemma _ ['a] (x,y,z : 'a) : Foo x y z.
Proof.
  checkfail apply foo2 exn ApplyMatchFailure.
  apply foo1.
Qed.

(* --------------------------------------------------------- *)
predicate P ['a] {S1 S2} {S1: x : 'a} {S2: y : 'a}.

global axiom [default] p_default ['a] (x, y : 'a) : P x y.

global lemma [default] _ : P empty empty.
Proof. 
  checkfail have ? := p empty (frame@init) exn Failure.
  checkfail have ? := p (frame@init) empty exn Failure.
  checkfail have ? := p empty (diff(empty,empty)) exn Failure.
  checkfail have ? := p (diff(empty,empty)) empty exn Failure.
  have A := p_default empty empty.  
  assumption A.
Qed.

global lemma [default] _ : P empty empty.
Proof. 
  apply p_default empty empty.  
Qed.

global lemma [default] _ : P empty empty.
Proof. 
  apply p_default empty.  
Qed.

global lemma [default] _ : P empty empty.
Proof. 
  apply p_default.  
Qed.

(* --------------------------------------------------------- *)
global lemma [default] _ ['a] (x,y : 'a) : P x y.
Proof. 
  checkfail have ? := p empty (frame@init) exn Failure.
  checkfail have ? := p (frame@init) empty exn Failure.
  checkfail have ? := p x (diff(x,y)) exn Failure.
  checkfail have ? := p (diff(x,y)) y exn Failure.
  have A := p_default x y.
  assumption A.
Qed.

global lemma [default] _ ['a] (x,y : 'a) : P x y.
Proof. 
  apply p_default x y.
Qed.

global lemma [default] _ ['a] (x,y : 'a) : P x y.
Proof. 
  apply p_default x.
Qed.

global lemma [default] _ ['a] (x,y : 'a) : P x y.
Proof. 
  apply p_default.
Qed.

(* --------------------------------------------------------- *)
global axiom pany in [any/default] ['a] (x, y : 'a) : P x y.

global lemma [any/default] _ ['a] (x,y : 'a) : P x y.
Proof. 
  checkfail have ? := pany empty (frame@init) exn Failure.
  checkfail have ? := pany (frame@init) empty exn Failure. 
  have A := pany x y.
  assumption A.
Qed.

global lemma [any/default] _ ['a] (x,y : 'a) : P x y.
Proof. 
  apply pany.
Qed.

(* --------------------------------------------------------- *)
system P1 = null.

global axiom [set: P1; equiv:default] p1 ['a] (x, y : 'a) : P x y.
(* same lemma as `p1`, but using different default systems (which are
   irrelevant here) *)
global axiom [any] p1_any ['a] (x, y : 'a) : P{[P1] [default]} x y.

global lemma [set: P1; equiv:default] _ ['a] (x,y : 'a) : P x y /\ P x y.
Proof. 
  split. 
  + have A := p_default x y.
    checkfail assumption A exn NotHypothesis. (* wrong systems *)
  
    have A1  := p1 x y.
    assumption A1.
  + have A1  := pany x y.
    assumption A1.
Qed.

global lemma [set: P1; equiv:default] _ ['a] (x,y : 'a) : P x y /\ P x y.
Proof. 
  checkfail apply p_default exn ApplyMatchFailure.
  split.  
  + apply pany.
  + apply p1.
Qed.

(* --------------------------------------------------------- *)
global axiom [any/default] pp ['a] (x, y : 'a) : 
  P{[P1] [default]} x y -> P x y.

global lemma [any/default] _ ['a] (x,y : 'a) : P x y.
Proof. 
  have ? := pp x y. 
  have ? := pp empty empty _; 1: by apply p1_any. 
  have ? := pp empty empty _; 1: by apply p1_any empty empty. 
  have A := pp x y _; 1: by apply p1_any x y.
  assumption A.
Qed.

global lemma [any/default] _ ['a] (x,y : 'a) : P x y.
Proof. 
  have ? := pp x y _. { 
    checkfail apply p_default exn NoAssumpSystem. 
    checkfail apply p1 exn NoAssumpSystem. 
    apply p1_any.
  }.
  assumption H.
Qed.

global lemma [any/default] _ ['a] (x,y : 'a) : P x y.
Proof. 
  apply pp _ _ _. 
  apply p1_any.
Qed. 

global lemma [any/default] _ ['a] (x,y : 'a) : P x y.
Proof. 
  apply pp _ _.
  apply p1_any.
Qed. 

global lemma [any/default] _ ['a] (x,y : 'a) : P x y.
Proof. 
  apply pp _.
  apply p1_any.
Qed. 

global lemma [any/default] _ ['a] (x,y : 'a) : P x y.
Proof. 
  apply pp.
  apply p1_any.
Qed.

(* --------------------------------------------------------- *)
(* stronger version of `pp` *)
global axiom pps 
  {P[like default]}
  in [any/default]
  ['a] (x, y, z : 'a) 
: 
  P{[P1] [default]} x (diff(y,z)) -> P{[P] [default]} x (diff(y,z)).

(* stronger version of `p1` *)
global axiom [set: P1; equiv:default] p1s ['a] (x, y, z : 'a) : P x (diff(y,z)).

global lemma [any/default] _ ['a] (x,y : 'a) : P empty (frame@init).
Proof. 
  checkfail apply pp exn Failure. (* bad variable instantiation *)
  admit. 
Qed.

global lemma _
  { P0 [like default] }
  in [set: P1; equiv:default]
  ['a] (x,y : 'a)
:
  P{[P0][default]} x (diff(x,y)).
Proof. 
  apply pps.
  checkfail apply p1 exn Failure. (* bad variable instantiation *)
  apply p1s.
Qed.

global lemma _
  { P0 [like default] }
  in [set: P1; equiv:default]
  ['a] (x,y : 'a)
:
  P{[P0][default]} x (diff(x,y)).
Proof.
  apply pps _ _ _.
  checkfail apply p1 exn Failure. (* bad variable instantiation *)
  apply p1s.
Qed.

(* --------------------------------------------------------- *)
predicate Q {set} {set: (x : message)} = [x = empty].

global lemma [set: P1; equiv:default] _ : Q{[P1]} empty.
Proof.
  rewrite /Q.
  auto.
Qed.

(* cannot expand `Q`, as `default <> P1`. *)
global lemma [set: P1; equiv:default] _ : Q{[default]} empty.
Proof.
  checkfail rewrite /Q exn Failure.
Abort.  
