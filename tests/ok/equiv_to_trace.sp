abstract p : message -> message
abstract a : message

system null.

name n : message.
name m : message.

global lemma [default/left,default/left] _ (x:message) : 
  [x=empty] -> 
  [m = empty] ->
  ([x=empty] -> equiv(diff(n,m))) -> 
  [n = empty].
Proof.
  nosimpl intro H1 H2 H3.
  byequiv.
  (* [x=empty] should still be there as a global assumption,
     otherwise [H1] will be unusable. *)
  rewrite equiv H3. 
  - assumption H1. 
  - assumption H2.
Qed.
