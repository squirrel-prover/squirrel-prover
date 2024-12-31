(*------------------------------------------------------------------*)
abstract a : message
abstract b : message
abstract c : message
abstract d : message
abstract e : message

abstract ok : index   -> message
abstract f  : message -> message
channel ch

system A: !_i in(ch,x);out(ch,<ok(i),x>).

abstract even : message -> boolean.

(*------------------------------------------------------------------*)
(* reach *)

lemma _ :
 (forall (x,y : message), y = a || x = b).
Proof.
  intro x y. 
  set a0 := a.

  (* we generalize to make sure that we `set` abstracted the correct
  occurrences *)
  generalize a0.
  have Ass : (forall a0, y = a0 || x = b) by admit.
  assumption Ass.
Qed.

lemma _ :
 (forall (x,y : message), x = a || y = b).
Proof.
  intro x y.
  set E := _ = a.

  generalize E.
  have Ass : (forall E, E || y = b) by admit.
  assumption Ass.
Qed.

lemma _ :
 (forall (y,x : message), f(x) = a || f(y) = b).
Proof.
  intro y x.
  set E := f _.
  set E1 := f _.

  generalize E E1.
  have Ass : (forall E E1, E = a || E1 = b) by admit.
  assumption Ass.
Qed.

(*------------------------------------------------------------------*)
abstract P : message -> bool.

(*------------------------------------------------------------------*)
axiom foo_glob (x : message[glob]) : P x.

global lemma _ x : [P x] /\ equiv(false).
Proof.
  set E := P x.

  generalize E.
  ghave Ass : Forall (E0:bool), [E0] /\ equiv(false) by admit.
  assumption Ass.
Qed.

global lemma _ t : [P (frame@t)].
Proof. 
  set E := frame@t.

  generalize E.
  have Ass : forall (E0:message), P E0 by admit.
  assumption Ass.
Qed.


(*------------------------------------------------------------------*)
lemma [any] _ ['a 'b] (phi,phi': 'a -> _) : 
  (exists i, phi i) && exists i, phi' i.
Proof.
  set E  := (exists _, _).
  set E1 := (exists _, _).

  generalize E E1.
  have Ass : forall E E1, E && E1 by admit.
  assumption Ass.
Qed.

(* same, but with the same formula [phi i] both times *)
lemma [any] _ ['a 'b] (phi: 'a -> _) : 
  (exists i, phi i) && exists i, phi i.
Proof.
  set E  := (exists _, _).
  checkfail set E1 := (exists _, _) exn Failure. (* no occurrences found *)

  generalize E.
  have Ass : forall E, E && E by admit.
  assumption Ass.
Qed.

(*------------------------------------------------------------------*)
(* We are in the system `any`, thus `set <> equiv`. Consequently,
    we can only abstract in `equiv(_)`. *)
global lemma [any] _ ['a 'b] (phi,phi': 'a -> _) : 
  (* *) [(exists i, phi i) && exists i, phi' i] /\
  equiv ((exists i, phi i) && exists i, phi' i).
Proof.
  set E  := exists _, _.
  set E1 := exists _, _.

  generalize E E1.
  ghave Ass :
  Forall (E2,E3:bool[glob]),
    [(exists (i:'a), phi i) && exists (i:'a), phi' i] /\ equiv(E2 && E3) 
  by admit.
  assumption Ass.
Qed.

(*------------------------------------------------------------------*)
system Q = null.

(* Same as previous lemma, but in the system `Q`.
   Here, we know that `set = equiv = Q`, thus we can abstract 
   in both `[_]` and `equiv(_)`. *)
global lemma [Q] _ ['a 'b] (phi,phi': 'a -> _) : 
  (* *) [(exists i, phi i) && exists i, phi' i] /\
  equiv ((exists i, phi i) && exists i, phi' i).
Proof.
  set E  := exists _, _.
  set E1 := exists _, _.

  generalize E E1.
  ghave Ass :
    Forall (E2,E3:bool), [E2 && E3] /\ equiv(E2 && E3) 
    by admit.
  assumption Ass.
Qed.

(*------------------------------------------------------------------*)
system Q0 = null.

(* We now have two systems `Q` and `Q0`, but in which system we abstract. *)
global lemma _ @set:Q @equiv:Q0 ['a 'b] (phi,phi': 'a -> _) : 
  (* *) [(exists i, phi i) && exists i, phi' i] /\
  equiv ((exists i, phi i) && exists i, phi' i).
Proof.
  (* by default, in `pair=Q0` *)
  set E  := exists _, _.
  set E1 := exists _, _.

  (* now in `set=Q` *)
  set E2 @system:Q := exists _, _.
  set E3 @system:Q := exists _, _.

  (* currently, we cannot generalize only in the `set` system, so we
     cannot check further that everything went well. *) 
Abort.
