lemma [any] _ x y (z : index): 
  let z = <x,y> in
  let z = <z,<x,y>> in
  z = <<x,y>,<x,y>>.
Proof.  
  intro ??. simpl. 
  checkfail simpl; true exn Failure.
  (* `simpl` does not open definitions by default 

     Crucially, this test must not be done after including `Core`, as
     this would add `eq_refl` as a rewrite hint, which would simplify
     the equality. *)

  simpl ~def; true.
Qed.

global lemma _ {P:system[pair]} @system:P x y (z : index): 
  Let z = <x,y> in
  Let z = <z,<x,y>> in
  [z = <<x,y>,<x,y>>].
Proof.  
  intro ??. 
  checkfail simpl; true exn Failure.
  (* `simpl` does not open definitions by default *)

  simpl ~def; true.
Qed.
