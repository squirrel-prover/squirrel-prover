include Core.
include Real. open Real.

channel c

system (in(c,x);out(c,x) | !_i in(c,x);out(c,x)).

lemma _ (t:timestamp) :
  t = init || (t = A || exists (i:index), t = A1(i)).
Proof.
  case t => _.  
  by left. 
  by right; left. 
  by right; right. 
Qed.

(* global case fails without *)
global lemma _ (t:timestamp) :
  [t = init] \/ [t = A || exists (i:index), t = A1(i)].
Proof.
  checkfail case t exn Failure. (* not [const] *)
Abort.

(* global case succeeds assuming `const` *)
global lemma _ (t:timestamp[const]) :
  [t = init] \/ [t = A] \/ [exists (i:index), t = A1(i)].
Proof.
  case t => H.
  + by left. 
  + by right; left. 
  + right; right. 
    destruct H as [i _]. 
    by exists i.
Qed.

(*------------------------------------------------------------------*)
type fin_t[finite].

inductive t = L : t | R : fin_t -> t.

lemma _ @system:any (t:t) :
  (t = L || exists i, t = R i).
Proof.
  case t.
  + left; auto.
  + intro i; right; exists i; auto.
Qed.

(*------------------------------------------------------------------*)
(* test the concrete version of `case` *)
namespace Concrete.
  lemma _ @system:any (t:t) :
    (t = L || exists i, t = R i) <: z.
  Proof. 
    case t => //=.
    + intro x. 
      right.
      by exists x.
  Qed.
  
  (* generic matcher over `t` *)
  let t_match
    (f_L : Real.t)
    (f_R : _ -> Real.t)
    (x : t)
   : Real.t
  with
    | L -> f_L
    | R i -> f_R i.

  axiom [any] refl_le_real (x : Real.t) : x <= x <: Real.z.
  
  system null.

  global lemma _ @set:default/left (t:t) pL pR rl (rr : Real.t) :
    [pL L <: rl] ->
    (Forall i, [pR (R i) <: rr]) ->
    [
      (t = L && pL t) || exists i, t = R i && pR t 
      <: rl + rr
    ].
  Proof.
    intro Hl Hr.
    case t <: rl, rr. 
    + left; simpl. 
      assumption Hl.
    + intro x.
      right; exists x. 
      simpl.
      have G := Hr x. 
      (* apply Hr. *) (* FIXME: concrete: why doesn't this work? *)
      assumption G. 
    + auto.
  Qed.

  (*------------------------------------------------------------------*)
  inductive int_list = 
    | N : int_list
    | C : int -> int_list -> int_list.

  axiom is_adv0 @system:any  (x:int[adv]) : true.
  axiom is_adv1 @system:any  (x:int_list[adv]) : true.

  global lemma _ @set:default/left (l:int_list[adv]) rl rr:
    [ l = N || exists x l', l = C x l' <: rl + rr ].
  Proof.
    id.
    case l <: rl, rr. 
    + left; simpl. admit.
    + intro x l'.
      right; exists x, l'. 
      simpl.

     (* both tests fail because `case` cannot keep the `adv` tag on `x,l'` *)
      checkfail have ? := is_adv0 x  exn Failure.
      checkfail have ? := is_adv1 l' exn Failure.
      admit.
    + auto.
  Qed.

  (* same as above, using `case ~tags`, which can keep the `adv` tag *)
  global lemma _ @set:default/left (l:int_list[adv]) rl rr:
    [ l = N || exists x l', l = C x l' <: rl + rr ].
  Proof.
    id.
    case ~tags l <: rl, rr. 
    + left; simpl. admit.
    + right; exists x, x0. 
      simpl.
      have ? := is_adv0 x.
      have ? := is_adv1 x0.
      admit.
    + auto.
  Qed.

  (*------------------------------------------------------------------*)
  (* Same two tests, but for the asymptotic logic. 
     These tests are in the `Concrete` namespace, 
     which is weird, but having them close to their 
     concrete counter-parts makes sense. *)
  global lemma _ @set:default/left (l:int_list[adv]):
    [ l = N || exists x l', l = C x l'].
  Proof.
    id.
    case l.
    + left; simpl. admit.
    + intro x l'.
      right; exists x, l'. 
      simpl.

     (* both tests fail because `case` cannot keep the `adv` tag on `x,l'` *)
      checkfail have ? := is_adv0 x  exn Failure.
      checkfail have ? := is_adv1 l' exn Failure.
      admit.
  Qed.


  (* same as above, using `case ~tags`, which can keep the `adv` tag *)
  global lemma _ @set:default/left (l:int_list[adv]) :
    [ l = N || exists x l', l = C x l'].
  Proof.
    id.
    case ~tags l.
    + left; simpl. admit.
    + right; exists x, x0. 
      simpl.
      have ? := is_adv0 x.
      have ? := is_adv1 x0.
      admit.
  Qed.
end Concrete.

(*------------------------------------------------------------------*)
(* tuples *)
lemma _ @system:any ['a 'b] (t: 'a * 'b) : exists x y, t = (x,y).
Proof.
  case t => x y.
  by exists x, y.
Qed.

(*------------------------------------------------------------------*)
inductive tree a =
| leaf : tree a
| node : a -> tree a -> tree a -> tree a.

lemma _ @system:any ['a] (x : 'a) (t : tree 'a) :
  t = leaf || exists a tl tg, t = node a tl tg.
Proof.
  case t.
  + by left.
  + by intro a tl tg; right; exists a, tl, tg.
Qed.
