abstract p : message -> message
abstract a : message

system null.

global goal [default/left,default/left] _ (x:message) : 
  [x=empty] -> 
  ([x=empty] -> equiv(diff(false,true))) -> 
  [False].
Proof.
  nosimpl intro H1 H2.
  byequiv.
  (* [x=empty] should still be there as a global assumption,
     otherwise [H2] will be unusable. *)
  rewrite equiv H2.
  assumption. 
  assumption.
Qed.
