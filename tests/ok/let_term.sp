include Basic.

lemma [any] _ x y : let z = <x,y> in z = <x,y>.
Proof.
  auto.
Qed.

lemma [any] _ (x : message) y : let x = y in <x,y> = <y,y>.
Proof.
  reduce ~flags:[zeta].
  apply eq_refl.
Qed.

lemma [any] _ x : (let x = <x,x> in let x = <x,x> in x) = <<x,x>,<x,x>>.
Proof.
  reduce ~flags:[zeta].
  apply eq_refl.
Qed.

(*------------------------------------------------------------------*)
lemma [any] _ x : let y = <x,x> in (y = <x,x>).
Proof.
  intro y.
  reduce ~flags:[def].
  apply eq_refl.
Qed.

(*------------------------------------------------------------------*)
(* intro *)

lemma [any] _ x y (z : index): 
  let z = <x,y> in
  let z = <z,<x,y>> in
  z = <<x,y>,<x,y>>.
Proof. 
  checkfail intro z exn Failure.

  intro z0.
  checkfail clear z0 exn Failure.
  revert z0.

  intro z0.
  revert z0.
Abort.

lemma [any] _ x y (z : index): 
  let z = <x,y> in
  let z = <z,<x,y>> in
  z = <<x,y>,<x,y>>.
Proof.  
  intro ??.
  reduce ~def.
  true.
Qed.

lemma [any] _ x y (z : index): 
  let z = <x,y> in
  let z = <z,<x,y>> in
  z = <<x,y>,<x,y>>.
Proof.  
  intro ??. 
  checkfail simpl; true exn Failure.
  (* `simpl` does not open definitions by default *)

  simpl ~def; true.
Qed.

lemma [any] _ x y (z : index): 
  let z = <x,y> in
  let z = <z,<x,y>> in
  z = <<x,y>,<x,y>>.
Proof.  
  intro ??. 
  auto ~def.
Qed.

lemma [any] _ x y (z : index): 
  let z = <x,y> in
  let z = <z,<x,y>> in
  z = <<y,y>,<x,y>>.            (* changed `x` into `y` *)
Proof.  
  intro ??. 
  checkfail reduce; true exn Failure.
  checkfail simpl; true exn Failure. 
  checkfail auto exn GoalNotClosed.
Abort.

(*------------------------------------------------------------------*)
(* global let *)

system null.

global lemma _ x y (z : index): 
  Let z = <x,y> in
  Let z = <z,<x,y>> in
  [z = <<x,y>,<x,y>>].
Proof. 
  checkfail intro z exn Failure.

  intro z0.
  checkfail clear z0 exn Failure.
  revert z0.

  intro z0.
  revert z0.
Abort.

global lemma _ x y (z : index): 
  Let z = <x,y> in
  Let z = <z,<x,y>> in
  [z = <<x,y>,<x,y>>].
Proof.  
  intro ??. 
  reduce ~def.
  true.
Qed.

global lemma _ x y (z : index): 
  Let z = <x,y> in
  Let z = <z,<x,y>> in
  [z = <<x,y>,<x,y>>].
Proof.  
  intro ??. 
  checkfail simpl; true exn Failure.
  (* `simpl` does not open definitions by default *)

  simpl ~def; true.
Qed.

global lemma _ x y (z : index): 
  Let z = <x,y> in
  Let z = <z,<x,y>> in
  [z = <<x,y>,<x,y>>].
Proof.  
  intro ??. 
  auto ~def.
Qed.

global lemma _ x y (z : index): 
  Let z = <x,y> in
  Let z = <z,<x,y>> in
  [z = <<y,y>,<x,y>>].            (* changed `x` into `y` *)
Proof.  
  intro ??. 
  checkfail reduce; true exn Failure.
  checkfail simpl; true exn Failure. 
  checkfail auto exn GoalNotClosed.
Abort.

(*------------------------------------------------------------------*)
abstract one : message.

channel c.
system [P0] A: out(c,zero).
system [P1] A: out(c,one).

global lemma [set:P1; equiv:P0] _ :
  [happens(A)] -> 
  Let z = output@A in
  equiv(diff(z,zero)) ->
  equiv(z) ->
  [z = zero].
Proof.
  intro H z H0 H1.
  rewrite /z in H1.

  rewrite /z in H0.

  checkfail rewrite /z exn Failure.
  (* Currently, we cannot expand `z`, as we are in the 
     wrong system (`P1`) *)

  (* apply eq_ref. *)
Abort.

global lemma [set:P1; equiv:P1] _ :
  [happens(A)] -> 
  Let z = output@A in
  equiv(diff(z,zero)) ->
  equiv(z) ->
  [z = zero].
Proof.
  intro H z H0 H1.
  rewrite /z in H1.
  checkfail auto exn GoalNotClosed.
  rewrite /z.  
  rewrite /output.
Abort.

global lemma [set:P0; equiv:P0] _ :
  [happens(A)] -> 
  Let z = output@A in
  equiv(diff(z,zero)) ->
  equiv(z) ->
  [z = zero].
Proof.
  intro H z H0 H1.
  rewrite /z in H1.
  rewrite /z.
  apply eq_refl.
Qed.

(* trivial check *)
global lemma [set:P1; equiv:P1] _ :
  [happens(A)] -> 
  Let z = output@A in
  [z = one] /\ equiv(z).
Proof.  
  intro H z.
  split.
  + rewrite /z /output; apply eq_refl. 
  + rewrite /z /output. auto. 
Qed.

(* trivial check *)
global lemma [set:P0; equiv:P0] _ :
  [happens(A)] -> 
  Let z = output@A in
  equiv(z).
Proof. 
  nosimpl intro H z.

  trans [P1]. 
  (* some of the goals below could succeed if we projects when rewriting 
     a defined variable *) 
  + checkfail rewrite /z exn Failure.
    admit. 
  + checkfail rewrite /z exn Failure.
    admit.
  + checkfail rewrite /z exn Failure.
    admit.
Qed.

global lemma [set:P1; equiv:P1] _ :
  [diff(one, zero) = zero] ->
  [happens(A)] -> 
  Let z = diff(output@A,zero) in
  equiv(diff(z,zero)) ->
  equiv(z) ->
  [z = zero].
Proof.
  intro A H z H0 H1.
  rewrite /z in H1.
  rewrite /z in H0.
  checkfail clear A; auto exn GoalNotClosed.
  rewrite /z. 
  checkfail clear A; by rewrite /output exn GoalNotClosed.
  rewrite /output.
  assumption A.
Qed.

(*------------------------------------------------------------------*)
lemma [any] choose_or_not ['a] (x,y : 'a) :
  (y <> x) =>
  let b = (fun z => (z = x || z = y)&& z <> x) in
  (choose b = y).
Proof.
  intro H b.
  assert (forall z, b z => (z = y)). {
    intro z Heq.
    rewrite /b /= in Heq. 
    destruct Heq.
    by case H0.
  }.
  apply H0.
  
  by rewrite /* (choose_spec (fun z => (z = x || z = y) && z <> x) y) /=.
Qed. 

global lemma _ (x,y : index): 
  [x <> y] -> equiv(true).
Proof.
  intro H.
  assert choose (fun t => (t = x || t = y) && t <> x) = y.

  have A /= := choose_or_not x y.
  by apply A.
  auto.
Qed.

global lemma _ (x,y : index): 
  [x <> y] -> equiv(true).
Proof.
  intro H.
  assert choose (fun t => (t = x || t = y) && t <> x) = y.
  by apply choose_or_not.
  auto.
Qed.

(*------------------------------------------------------------------*)
(* same as `choose_or_not`, inversing the `let` and `=>` *)
lemma [any] choose_or_not2 ['a] (x,y : 'a) :
  let b = (fun z => (z = x || z = y)&& z <> x) in
  (y <> x) =>
  (choose b = y).
Proof.
  intro b H.
  assert (forall z, b z => (z = y)). {
    intro z Heq.
    rewrite /b /= in Heq. 
    destruct Heq.
    by case H0.
  }.
  apply H0.
  
  by rewrite /* (choose_spec (fun z => (z = x || z = y) && z <> x) y) /=.
Qed. 

global lemma _ (x,y : index): 
  [x <> y] -> equiv(true).
Proof.
  intro H.
  assert choose (fun t => (t = x || t = y) && t <> x) = y.

  have A /= := choose_or_not2 x y.
  by apply A.
  auto.
Qed.

global lemma _ (x,y : index): 
  [x <> y] -> equiv(true).
Proof.
  intro H.
  assert choose (fun t => (t = x || t = y) && t <> x) = y.
  by apply choose_or_not2.
  auto.
Qed.

(*------------------------------------------------------------------*)
lemma [any] _ : let x = empty in x = empty.
Proof. 
  intro x. 
  have A : x = empty. auto. 
  checkfail rewrite -A in x exn Failure. (* cannot target definitions *)
Abort.

(*------------------------------------------------------------------*)
lemma [P0] _ :
  let y = zero in 
  let y = y    in
  let y = y    in
  y = zero.
Proof.
  intro y y1 y2. 
  rewrite /y2 /y1 /y.
  apply eq_refl.
Qed.

(*------------------------------------------------------------------*)
(* Test crypto *)

hash h.

name k : message.

lemma [P0] _ (m : _[adv]): 
  let x = h(zero, k) in 
  let y = h(one , k) in 
  att(<x,y>) = h(m,k) => m = zero || m = one.
Proof.
  intro x y H.
  euf H.
  + auto. 
  + auto.
Qed.

lemma [P0] _ (m : _[adv]): 
  let x = h(zero, k) in 
  let y = h(<one,x>,  k) in 
  att(<y,x>) = h(m,k) => m = zero || m = <one,x>.
Proof.
  intro x y H.
  euf H.
  + auto. 
  + auto.
Qed.

lemma [P0] _ (m : _[adv]): 
  let x = h(zero, k) in 
  let y = h(<one,x>,  k) in 
  att(y) = h(m,k) => m = zero || m = <one,x>.
Proof.
  intro x y H.
  euf H.
  + auto. 
  + auto.
Qed.

(*------------------------------------------------------------------*)
global axiom ax : 
  Let y = false in 
  equiv(y).

(* check that matching is modulo `let` reduction *)
global lemma _ : 
  equiv(false).
Proof.
  apply ax.
Qed.

(*------------------------------------------------------------------*)

global axiom ax1 : 
  Let y = false in 
  ( Let x = true in
    equiv(diff(x,false))       ) -> 
  equiv(y).

(* check that matching is modulo `let` reduction *)
global lemma _ : 
  equiv(diff(true,false)) ->
  equiv(false).
Proof.
  intro H.
  apply ax1.
  apply H.
Qed.
