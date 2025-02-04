system null.

global lemma _ ['a] (x,y,z : 'a) : [x = y] -> [x = z => false].
Proof. 
  intro H. 
  intro G. 
  (* We are not allowed to rewrite a local hypothesis in a global 
     hypothesis! *)
  checkfail rewrite G in H exn NothingToRewrite.
Abort.

axiom foo : 42 = 24 => 1 = 2.

global lemma _ : [1 = 3] -> [42 = 24 => 1 = 3].
Proof.
  intro H. intro G.

  checkfail have A := foo G; rewrite A in H exn NothingToRewrite.
  (* cannot rewrite local equalities in global assumptions *)

  checkfail rewrite (foo G) in H exn NothingToRewrite.
  (* idem, using a proof-term *)
Abort.

global lemma _ : [1 = 3] -> [42 = 24] -> [1 = 3].
Proof.
  nosimpl intro H G.
 nosimpl rewrite (foo _) in H.
 + assumption.
 + rewrite -(foo _) in H.
    ++ assumption.
    ++ checkfail have A := foo G; rewrite A in H exn NothingToRewrite.
         (* cannot rewrite local equalities in global assumptions *)

         rewrite (foo G) in H.
         (* idem, using a proof-term *)
Abort.

axiom bar : 1 = 2.

global lemma _ :  [1 = 3] -> [false].
Proof.
  intro H.
  rewrite bar in H.
Abort.

name t : int.
global axiom foo1 : [t = 24] -> [1 = 2].
axiom foo2 : t = 24 => 2 = 1.
global lemma _ : [1 = 3] -> [t = 24 =>  1 = 3].
Proof.
  intro H. intro G.
 nosimpl rewrite (foo1 _ ) in H.
 checkfail assumption exn NotHypothesis. admit.

 nosimpl rewrite (foo2 _) in H.
 checkfail assumption exn NotHypothesis. admit.

 nosimpl rewrite -(foo2 _) in *.
 checkfail assumption exn NotHypothesis. admit.

nosimpl rewrite (foo2 _).
assumption.

Abort.
