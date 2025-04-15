include Core.

(* ------------------------------------------------------------------- *)

(* `Non-deduction` or weak-secrecy *)
predicate ( *> ) ['a 'b] {set:system} {set: (u : 'a, m : 'b)} =
  Forall (f : _[adv]), [f u <> m].

(* ------------------------------------------------------------------- *)
(* empty system used because the following global goals do not 
   care about the `equiv` component system context. *)
system none = null.

(* ------------------------------------------------------------------- *)
(* 
# Reasoning rules on Non-deduction and Deduction
*)

namespace Deduction.

global lemma d_refl @system:any ['a] (u : 'a) : 
 $(u |> u).
Proof.
rewrite /(|>).
exists (fun x => x) => //.
Qed.

global lemma s_right_fa @system:any
 ['a 'b 'c] (u : 'a, v : 'b, g : 'b -> 'c) 
: 
    $( u *> v ) ->
    (Exists (ginv : _ [adv]), [ginv u (g v) = v]) ->
    $( u *> (g v) ).
Proof.  
  intro Ded [ginv Hginv].
  rewrite /( *> ) => f.
  intro Eq.
  apply f_apply (fun (x : 'c) => ginv u x) in Eq.
  rewrite /= Hginv in Eq.
  rewrite /( *> ) in Ded.
  have ? /= := Ded (fun (u : 'a) => ginv u (f u)).
  auto.
Qed.

global lemma s_left_fa @system:any ['a 'b 'c 'd] (u : 'a) (v : 'b, f : 'a -> 'c[adv]) : 
   $( u *> v ) ->
   $( (f u) *> v ).
Proof.
  intro @/( *> ) H g.
  apply H (fun x => g (f x)).
Qed.

(* ------------------------------------------------------------------- *)
global lemma d_nd @system:any ['a 'b] (u : 'a) (v : 'b) : 
    $(u *> v) ->
    $(u |> v) ->
    [false].
Proof.
  intro @/( *> ) @/( |> ) H [f G].
  by have ? := H f. 
Qed.

global lemma neq @system:any ['a 'b] (u : 'a) (v, w : 'b) :
    $(u |> v) ->
    $( u *> w) ->
    [v <> w].
Proof.
  intro @/( |> ) @/( *> ) [f H1] H2.
  by have ? := (H2 f).
Qed.

global lemma [any]
  s_weak_l ['a 'b 'c] (u : 'a) (v : 'b) (w : 'c) : 
    $(u |> v) ->
    $(u *> w) ->
    $(v *> w).
Proof.
  intro @/( |> ) @/( *> ) [f H1] H2 g.
  have A /= := H2 (fun x => g(f x)).
  rewrite H1 in A.
  assumption A.
Qed.

global lemma [any] 
  s_weak_r ['a 'b 'c] (u : 'a) (v : 'b) (w : 'c) : 
    $(u *> w) ->
    $(v |> w) ->
    $(u *> v).
Proof.
  intro @/( |> ) @/( *> ) H1 [f H2] g.
  have A /= := H1 (fun x => f(g x)).
  auto.
Qed.

global lemma [any] d_trans ['a 'b 'c] (u : 'a) (v : 'b) (w : 'c) :
  $(u     |> v) ->
  $((u,v) |> w) ->
  $(u     |> w).
Proof.
  intro @/( |> ) [f H] [f1 H1].
  exists (fun u => f1 (u, f u)). 
  reduce.
  rewrite H H1.
  apply eq_refl.
Qed.

(* ------------------------------------------------------------------- *)
(* Rule Rw:Equiv *)

global lemma [set: none/left; equiv:none/left,none/left] 
  RwEquiv ['a 'b] (u1, u2 : 'a) (v1, v2 : 'b) : 
    $(u2 *> v2)->
    equiv(diff(u1,u2), diff(v1,v2)) ->
    $(u1 *> v1).
Proof.
  intro Nded.
  intro equ.
  rewrite /( *> ) in *.
  intro f.
  ghave equ' : equiv(diff(f(u1) <> v1,f(u2) <> v2)). {
    fa 0; fa 0.
    deduce 0.
    auto.
  }.
  rewrite equiv equ'.
  by have C := Nded f.
Qed.

global lemma [set: none/left; equiv:none/left,none/left] 
  RwEquivWeak ['a 'b] (u1, u2 : 'a) (v1, v2 : 'b) : 
    $(u2 *> v2)->
    equiv(diff(u1,u2), (fun x => x=diff(v1,v2))) ->
    $(u1 *> v1).
Proof.
  intro Nded.
  intro equ.
  rewrite /( *> ) in *.
  intro f.

  ghave equ' : equiv(diff(f u1 <> v1,f u2 <> v2)). {
   
    have -> : forall (u:'a,v:'b), (f u <> v) = (fun x => not (x = v)) (f u) by auto.
    fa 0; fa 1. fa 0.
    deduce 1.
    auto.  
  }.

  rewrite equiv equ'.

  have C := Nded f. 
  auto.
Qed.


(* ------------------------------------------------------------------- *)
(* Rule Rw:Oracle *)

global axiom [any]
  RwOracle1 ['a 'b 'c 'd] (u : 'a) (t1, t2 : 'b -> 'c) : 
  (* Warning : 'd must be a simple type *)
    (Forall (f : 'a -> ('b -> 'c) -> 'b [adv]), [t1 (f u t1) = t2 (f u t1)]) ->
    (Forall (f : 'a -> ('b -> 'c) -> 'd [adv]), [f u t1 = f u t2]).

global lemma [any] 
  RwOracle2 ['a 'b 'c 'd] (u : 'a) (t1, t2 : 'b -> 'c) : 
    (Forall (f : 'a -> ('b -> 'c) -> 'b [adv]), [t1 (f u t2) = t2 (f u t2)]) ->
    (Forall (f : 'a -> ('b -> 'c) -> 'd [adv]), [f u t1 = f u t2]).
Proof.
  intro H.
  rewrite eq_sym .
  apply RwOracle1 u t2 t1.
  rewrite eq_sym.
  auto.
Qed.

end Deduction.

(* ------------------------------------------------------------------- *)
(*
# Frames
*)


global lemma frame_ded_past
 {P : system[pair]}
 @system:P
 (tau,tau':timestamp [const]) 
:
 [tau'<= tau] -> $( (frame@tau) |> (frame@tau')).
Proof.
  dependent induction tau.
  intro tau IH Ord.
  
  ghave [H1 | H2] : [tau=init || tau<>init] by auto.
  
  + ghave H2 : [tau'=init] by auto.
    rewrite H1 H2.
  
    rewrite frame_init.
    by have ? := Deduction.d_refl zero.
  
  + ghave [H3 | H4] : [tau=tau' || tau<>tau'] by auto.
    - rewrite H3.
      rewrite /(|>).
      by exists (fun x => x).
  
    - rewrite frame_not_init //.
      have ? // := IH (pred tau) _ _.
  
      rewrite / (|>) in *.
      destruct H.
      exists (fun x => f (fst x)) => //.
Qed.
