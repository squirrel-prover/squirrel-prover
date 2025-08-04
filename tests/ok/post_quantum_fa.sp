include Core.

(* --------------------------------------------------------- *)
system Q = null.

global lemma [Q] _ (f:message -> message) x :
 equiv(x) ->
 equiv(x, f x).
Proof.
  intro E.

  (* fails because `f` is not `adv` *)
  checkfail deduce 1 exn ApplyMatchFailure. 
Abort.

(* same lemma, but assuming that `adv(f)` *)
global lemma [Q] _ (f:message -> message[adv]) x :
 equiv(x) ->
 equiv(x, f x).
Proof.
  intro E.
  deduce 1.                       (* should succeed *)
  apply E.
Qed.

type A[serializable].

(* same lemma, but `f` inputs type is changed. *)
global lemma [Q] _ (f:A -> message[adv]) x :
 equiv(x) ->
 equiv(x, f x).
Proof.
  nosimpl intro E.
  deduce 1.
  apply E.
Qed.

(* This declares an abstract polymorphic operator `f`.

   Squirrel assumes that polymorphic operators are `adv` for all
   instantiation of `'a` as a classical type. *)
op f ['a] : 'a -> message.

global lemma [Q] _ (x : message) :
 equiv(x) ->
 equiv(x, f x).
Proof.
  nosimpl intro E.

  deduce 1. 
  (* since `f` is an operator applied to a classical type `message`,
     it is `adv`, and `deduce` succeeds  *)

  apply E.
Qed.

(* same as above, but `x` is of type `'a` for some arbitrary `'a` *)
global lemma [Q] _ ['a] (x : 'a) :
 equiv(x) ->
 equiv(x, f x).
Proof.
  nosimpl intro E.

  checkfail deduce 1 exn ApplyMatchFailure.
  (* since `f` is an operator applied to an type `'a` that could not
     be classical, we do not know that `f` is `adv`, and `deduce`
     fails *)

  checkfail fa 1 exn Failure.
  (* `fa` must fail for the same reason *)
Abort.

(* --------------------------------------------------------- *)
channel c.

mutable s = empty.

process P = 
  in(c,x); out(c,x).

system [postquantum] PQ = !_i P.

open Quantum.
close Classic.

(* --------------------------------------------------------- *)
(* We should not be able to prove the following lemma, as we are not
   in the PQ setting. *)

(* ensure that this is [false], even though it should be the default value *)
set postQuantumEquivs = false.

global lemma [PQ] _ (t:timestamp [const]) :
 [happens(t)] ->  equiv(frame@t).
Proof.
  intro Hap.
  induction t.
  + by expand.
  + rewrite /frame /state. 
    fa 0.
    fa 1.
    checkfail fa 1 exn Failure.
Abort.

(* --------------------------------------------------------- *)
set postQuantumEquivs = true.

global lemma [PQ] _ (t:timestamp [const]) :
 [happens(t)] ->  equiv(frame@t).
Proof.
  intro Hap.
  induction t.
  + by expand.
  + rewrite /frame /state.
    fa 0.
    fa 1.
    fa 1.
   (* Here, the name is not fresh, as it occures in the transcript ! 
      We should get the following freshness condition, impossible to prove.
    *)
    have A : 
     pred (P(i)) <> pred (P(i)) &&
      forall (t:timestamp), t < P(i) => pred (P(i)) <> pred t 
    by  admit.
    assumption A.
Abort.


global lemma [PQ] _ (t:timestamp [const]) :
 [happens(t)] ->  equiv(frame@t).
Proof.
  intro Hap.
  induction t.
  + by expand.
  + rewrite /frame /state /transcript /exec /cond /output /input .   
    fa 0.
    fa !<_,_>.
    deduce.

    nosimpl(fa 0). 
    (* Here, notice how frame element number 2 is a classical element,
       found in frame element 0. It disappears with `simpl`. *)
    simpl.

    (* quantum function application on `qatt` *)
    fa 0. 
    {
      have A : forall (t:timestamp), t < P(i) => pred (P(i)) <> pred t  by auto.
      (* the freshness condition is trivial *)
      assumption A.
    }.
    deduce 1. 
    assumption.
Qed.


global lemma [PQ] _ (t:timestamp [const]) :
 [happens(t)] ->  equiv(frame@t).
Proof.
  intro Hap.
  induction t.
  + by expand.
  + rewrite /frame /state /transcript /exec /cond /output /input .   
    fa 0.
    fa 2.
    fa 3.
    fa 4.
    deduce.

    (* Here, if we are in the same state as the previous lemma. But,
      instead of doing `fa` on `qatt(...)#2`, we do it on `qatt(...)#1`.
      It is not equivalent. *)
    nosimpl(fa 2).

    (* here, `simpl` MUST NOT work and get ride of `0`. Indeed, we have a
      duplication of a quantum state. *)
    simpl.
    deduce.

    ghave E :  
     equiv(qatt (qrnd (pred (P(i))), frame@pred (P(i)))#2,
     transcript@pred (P(i)),
     qatt (qrnd (pred (P(i))), frame@pred (P(i)))).
    by admit.  
    assumption E.
Qed.

set postQuantumEquivs=false.
