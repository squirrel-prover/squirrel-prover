predicate A {P:system}       {P : (x : message)}. 
predicate B {P:system[pair]} {P : (x : message)}. 

(*  *) axiom loc_lem {P:system} @system:P : false.

global axiom glob_lem1 {P:system[pair]} @system:P :
   A{P} empty /\ [false] /\ equiv(frame@init).

global axiom glob_lem2 {P:system,Q:system[pair]} @set:P @equiv:Q : 
  B{Q} empty /\ [false] /\ equiv(frame@init).

(*------------------------------------------------------------------*)
(* local lemma, no `equiv` field *)
lemma _ {P:system} @system:P : false.
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
lemma _ {P:system,Q:system[pair]} @set:P @equiv:Q : false.
Proof.
  have ? := loc_lem.
  checkfail have ? := glob_lem1 exn NoAssumpSystem. 
  (*`P` is not necessarily a pair, so applying this lemma would be
  unsound. *)

  have ? := glob_lem2.  
Abort.

(*------------------------------------------------------------------*)
system P1 = null.

(* in `P1/left` *)
lemma _ @system:P1/left : false.
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
lemma _ @system:P1 : false.
Proof.
  have ? := loc_lem. 
  checkfail have ? := glob_lem1 exn NoAssumpSystem. 
  (* Squirrel cannot infer `Q` *)

  checkfail have ? := glob_lem2 exn NoAssumpSystem. 
  (* cannot infer `Q` (this limitation could be lifted) *)
Abort.

(*------------------------------------------------------------------*)
(* local lemma, with an `equiv` field *)

lemma _ @set:P1 @equiv:P1 : false.
Proof.
  have ? := loc_lem.
  have ? := glob_lem1.
  have ? := glob_lem2.  
Abort.
