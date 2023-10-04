system null.

(* --------------------------------------------------------- *)
predicate Bar {}.

global axiom bar : $(Bar).

(* test `apply`, `have` and `assumption` *)

global lemma _  : $(Bar).
Proof.
  have A : $(Bar) by admit.
  apply A.
Qed.

global lemma _  : $(Bar).
Proof.
  apply bar.
Qed.

global lemma _  : $(Bar).
Proof.
  have A : $(Bar) by admit.
  assumption A.
Qed.

global lemma _  : $(Bar).
Proof. 
  have A := bar.
  assumption A.
Qed.

(* --------------------------------------------------------- *)
predicate Bar1 {}.

global axiom bar1 : $(Bar1).

(* negative checks for `have` and `apply` *)

global lemma _  : $(Bar1).
Proof.
  have A : $(Bar) by admit.
  checkfail apply A exn ApplyMatchFailure.
Abort.

global lemma _  : $(Bar1).
Proof.
  have A : $(Bar) by admit.
  checkfail assumption A exn NotHypothesis.
Abort.

(* --------------------------------------------------------- *)
predicate Foo ['a] {} (x : 'a) y z = [x = y && y = z].

global axiom foo1 ['a] (x,y,z : 'a) : $(Foo x y z).
global axiom foo2                   : $(Foo empty empty empty).

global lemma _ ['a] (x,y,z : 'a) : [false]. 
Proof. 
  have ? : $(Foo x y z).
  have ? : $(Foo empty empty empty).
Abort.

global lemma _ ['a] (x,y,z : 'a) : $(Foo x y z).
Proof.
  have -> : [x = y] by admit.
  have -> : [z = y] by admit.
  have A : $(Foo y y y) by admit.
  assumption A.
Qed.

global lemma _ ['a] (x,y,z : 'a) : $(Foo x y z).
Proof.
  have X  : x = y by admit.
  have X' : z = y by admit.
  rewrite X X'.
  have A : $(Foo y y y) by admit.
  assumption A.
Qed.

global lemma _ ['a] (x,y,z : 'a) : $(Foo x y z).
Proof.
  have A := foo1 x y z.
  assumption A.
Qed.

global lemma _ ['a] (x,y,z : 'a) : $(Foo x y z).
Proof.
  have A0 := foo1 x.
  have A  := A0 y z.
  assumption A.
Qed.

global lemma _ ['a] (x,y,z : 'a) : $(Foo x y z).
Proof.
  checkfail apply foo2 exn ApplyMatchFailure.
  apply foo1.
Qed.

(* --------------------------------------------------------- *)
predicate P ['a] {S1 S2} {S1: x : 'a} {S2: y : 'a}.

global axiom [set: default; equiv:default] p ['a] (x, y : 'a) : $(P x y).

global lemma [set: default; equiv:default] _ : $(P empty empty).
Proof. 
  checkfail have ? := p empty (frame@init) exn Failure.
  checkfail have ? := p (frame@init) empty exn Failure.
  checkfail have ? := p empty (diff(empty,empty)) exn Failure.
  checkfail have ? := p (diff(empty,empty)) empty exn Failure.
  have A := p empty empty.  
  assumption A.
Qed.

global lemma [set: default; equiv:default] _ : $(P empty empty).
Proof. 
  apply p empty empty.  
Qed.

global lemma [set: default; equiv:default] _ : $(P empty empty).
Proof. 
  apply p empty.  
Qed.

global lemma [set: default; equiv:default] _ : $(P empty empty).
Proof. 
  apply p.  
Qed.

(* --------------------------------------------------------- *)
global lemma [set: default; equiv:default] _ ['a] (x,y : 'a) : $(P x y).
Proof. 
  checkfail have ? := p empty (frame@init) exn Failure.
  checkfail have ? := p (frame@init) empty exn Failure.
  checkfail have ? := p x (diff(x,y)) exn Failure.
  checkfail have ? := p (diff(x,y)) y exn Failure.
  have A := p x y.
  assumption A.
Qed.

global lemma [set: default; equiv:default] _ ['a] (x,y : 'a) : $(P x y).
Proof. 
  apply p x y.
Qed.

global lemma [set: default; equiv:default] _ ['a] (x,y : 'a) : $(P x y).
Proof. 
  apply p x.
Qed.

global lemma [set: default; equiv:default] _ ['a] (x,y : 'a) : $(P x y).
Proof. 
  apply p.
Qed.

(* --------------------------------------------------------- *)
global axiom [set: any; equiv:default] pany ['a] (x, y : 'a) : $(P x y).

global lemma [set: any; equiv:default] _ ['a] (x,y : 'a) : $(P x y).
Proof. 
  checkfail have ? := pany empty (frame@init) exn Failure.
  checkfail have ? := pany (frame@init) empty exn Failure.
  have _ := p x y.
  have A := pany x y.
  assumption A.
Qed.

global lemma [set: any; equiv:default] _ ['a] (x,y : 'a) : $(P x y).
Proof. 
  apply pany.
Qed.

(* --------------------------------------------------------- *)
system [P1] null.

global axiom [set: P1; equiv:default] p1 ['a] (x, y : 'a) : $(P x y).

global lemma [set: P1; equiv:default] _ ['a] (x,y : 'a) : $(P x y).
Proof. 
  have A  := pany x y.
 (* wrong systems, and it does not matter that [P1 ⊆ any]! *)
  checkfail assumption A exn NotHypothesis.
  have A' := p x y.
  checkfail assumption A' exn NotHypothesis. (* wrong systems *)
  
  have A'' := p1 x y.
  assumption A''.
Qed.

global lemma [set: P1; equiv:default] _ ['a] (x,y : 'a) : $(P x y).
Proof. 
 (* wrong systems, and it does not matter that [P1 ⊆ any]! *)
  checkfail apply pany exn ApplyMatchFailure. 
  checkfail apply p exn ApplyMatchFailure.
  apply p1.
Qed.

(* --------------------------------------------------------- *)
global axiom [set: any; equiv:default] pp ['a] (x, y : 'a) : 
  $(P{[P1] [default]} x y) -> $(P x y).

global lemma [set: any; equiv:default] _ ['a] (x,y : 'a) : $(P x y).
Proof. 
  have ? := pp x y.

  have ? := pp empty empty _; 1: by apply p1. 
  have ? := pp empty empty _; 1: by apply p1 empty empty. 
  have A := pp x y _; 1: by apply p1 x y.
  assumption A.
Qed.

global lemma [set: any; equiv:default] _ ['a] (x,y : 'a) : $(P x y).
Proof. 
  have ? := pp x y _. {
    checkfail apply p exn ApplyMatchFailure.
    apply p1.
  }.
  assumption H.
Qed.

global lemma [set: any; equiv:default] _ ['a] (x,y : 'a) : $(P x y).
Proof. 
  apply pp _ _ _. 
  (* apply pp x y _. *)
  apply p1.
Qed. 

global lemma [set: any; equiv:default] _ ['a] (x,y : 'a) : $(P x y).
Proof. 
  apply pp _ _.
  apply p1.
Qed. 

global lemma [set: any; equiv:default] _ ['a] (x,y : 'a) : $(P x y).
Proof. 
  apply pp _.
  apply p1.
Qed. 

global lemma [set: any; equiv:default] _ ['a] (x,y : 'a) : $(P x y).
Proof. 
  apply pp.
  apply p1.
Qed.

(* --------------------------------------------------------- *)
(* stronger version of `pp` *)
global axiom [set: any; equiv:default] pps ['a] (x, y, z : 'a) : 
  $(P{[P1] [default]} x (diff(y,z))) -> $(P x (diff(y,z))).

(* stronger version of `p1` *)
global axiom [set: P1; equiv:default] p1s ['a] (x, y, z : 'a) : $(P x (diff(y,z))).

global lemma [set: any; equiv:default] _ ['a] (x,y : 'a) : $(P empty (frame@init)).
Proof. 
  checkfail apply pp exn Failure. (* bad variable instantiation *)
  (* TODO: system-annotations on macros *)
  (* apply pps _ (frame@init){default/left} (frame@init){default/right}. *)
  admit. 
Qed.

global lemma [set: P1; equiv:default] _ ['a] (x,y : 'a) : 
  $(P{[any][default]} x (diff(x,y))).
Proof. 
  apply pps.
  checkfail apply p1 exn Failure. (* bad variable instantiation *)
  apply p1s.
Qed.

global lemma [set: P1; equiv:default] _ ['a] (x,y : 'a) : 
  $(P{[any][default]} x (diff(x,y))).
Proof. 
  apply pps _ _ _.
  checkfail apply p1 exn Failure. (* bad variable instantiation *)
  apply p1s.
Qed.

(* --------------------------------------------------------- *)
predicate Q {set} {set: (x : message)} = [x = empty].

global lemma [set: P1; equiv:default] _ : $(Q{[P1]} empty).
Proof.
  rewrite /Q.
  auto.
Qed.

(* cannot expand `Q`, as `default <> P1`. *)
global lemma [set: P1; equiv:default] _ : $(Q{[default]} empty).
Proof.
  checkfail rewrite /Q exn Failure.
Abort.  
