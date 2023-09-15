abstract ok : message
name n : index -> message.

name n1 : index -> message.
name n2 : index -> message.
name n3 : index -> message.
name n4 : index -> message.
name n5 : index -> message.
name n6 : index -> message.
name n7 : index -> message.
name n8 : index -> message.
name n9 : index -> message.
name n10 : index -> message.


channel c.

process a (i:index) =
  out(c,ok)

system ( !_i A : a(i)).

(*------------------------------------------------------------------*)
(* simple first scenario with apply *)
global lemma _ (i:index[const]) :
  equiv(seq(j:index => n(j))) -> equiv(seq(j:index => n(j)), n(i)).
Proof.
  intro H.
  apply H.
Qed.

(* same using the `deduce` tactic *)
global lemma _ (i:index[const]) :
 equiv(seq(j:index => n(j))) ->
 equiv(seq(j:index => n(j)), n(i)).
Proof.
  intro H.
  checkfail by try assumption exn GoalNotClosed.
  deduce 1.
  assumption H.
Qed.

(* check failure of the above without the `const` assumption *)
global lemma _ (i:index) :
 equiv( 
  seq(j:index => n(j)),
  n(i)).
Proof.
  checkfail deduce 1 exn ApplyMatchFailure.
Abort.

(*------------------------------------------------------------------*)
(*Testing deduce can compute an element of a sequence. Many sequences added to test complexity, on small but non trivial instances.*)
global lemma _ (i:index[const]) :
 equiv( 
  seq(j:index => n(j)),
  seq(j:index => n1(j)),
  seq(j:index => n2(j)),
  seq(j:index => n3(j)),
  seq(j:index => n4(j)),
  seq(j:index => n5(j)),
  seq(j:index => n6(j)),
  seq(j:index => n7(j)),
  seq(j:index => n9(j)),
  seq(j:index => n9(j)),
  seq(j:index => n10(j)),
  n(i)).
Proof.
  deduce 11.
  admit.
Qed.

global lemma _ (i:index[const]) :
 equiv( 
  seq(j:index => n1(j)),
  seq(j:index => n2(j)),
  seq(j:index => n3(j)),
  seq(j:index => n4(j)),
  seq(j:index => n5(j)),
  seq(j:index => n6(j)),
  seq(j:index => n7(j)),
  seq(j:index => n9(j)),
  seq(j:index => n9(j)),
  seq(j:index => n10(j)),
  seq(j:index => n(j)),
  n(i)).
Proof.
  deduce 11.
  admit.
Qed.
