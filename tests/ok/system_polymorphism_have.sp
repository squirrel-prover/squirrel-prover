predicate A {P}       {P : (x : message)}. 
predicate B {P[pair]} {P : (x : message)}. 

(*  *) axiom loc_lem {P} in [P] : false.

global axiom glob_lem1 {P[pair]} in [P] :
   A{[P]} empty /\ [false] /\ equiv(frame@init).

global axiom glob_lem2 {P Q[pair]} in [set:P; equiv:Q] : 
  B{[Q]} empty /\ [false] /\ equiv(frame@init).

(*------------------------------------------------------------------*)
(* local lemma, no `equiv` field *)
lemma _ {P} in [P] : false.
Proof.
  have ? := loc_lem. 
  checkfail have ? := glob_lem1 exn NoAssumpSystem. 
  (*`P` is not necessarily a pair, so applying this lemma would be 
     unsound.
     Further, Squirrel cannot infer `Q` *)

  checkfail have ? := glob_lem2 exn NoAssumpSystem. 
  (* cannot infer `Q` (this limitation could be lifted) *)
Abort.

(*------------------------------------------------------------------*)
(* local lemma, with an `equiv` field *)
lemma _ {P Q[pair]} in [set:P; equiv:Q] : false.
Proof.
  checkfail have ? := loc_lem exn NoAssumpSystem. 
  (* Squirrel does not see that the lemma should apply because
     the lemma has no `equiv` component and can thus safely be interpreted in `Q`. *)

  checkfail have ? := glob_lem1 exn NoAssumpSystem. 
  (*`P` is not necessarily a pair, so applying this lemma would be
  unsound. *)

  have ? := glob_lem2.  
Abort.

(*------------------------------------------------------------------*)
system P1 = null.

(* in `P1/left` *)
lemma _ in [P1/left] : false.
Proof.
  have ? := loc_lem. 
  checkfail have ? := glob_lem1 exn NoAssumpSystem. 
  (*`P` is a pair, so applying this lemma would be 
     unsound.
     Further, Squirrel cannot infer `Q` *)

  checkfail have ? := glob_lem2 exn NoAssumpSystem. 
  (* cannot infer `Q` (this limitation could be lifted) *)
Abort.

(* in `P1` *)
lemma _ in [P1] : false.
Proof.
  have ? := loc_lem. 
  checkfail have ? := glob_lem1 exn NoAssumpSystem. 
  (* Squirrel cannot infer `Q` *)

  checkfail have ? := glob_lem2 exn NoAssumpSystem. 
  (* cannot infer `Q` (this limitation could be lifted) *)
Abort.

(*------------------------------------------------------------------*)
(* local lemma, with an `equiv` field *)

lemma _ in [set:P1; equiv:P1] : false.
Proof.
  checkfail have ? := loc_lem exn NoAssumpSystem. 
  (* Squirrel does not see that the lemma should apply because
     the lemma has no `equiv` component and can thus safely be 
     interpreted in `Q`. *)

  have ? := glob_lem1.
  have ? := glob_lem2.  
Abort.
