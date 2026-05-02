system default = null.

abstract a : message.
abstract b : message.
abstract c : message.

axiom lem @system:default : diff(a,b) = c.

global lemma _ @system:(default/left,default/right) : equiv(diff(a,c)).
Proof.
  (* rewrite under the diff, on the left *)
  nosimpl rewrite lem.
Abort.

global lemma _ @system:(default/right,default/left) : equiv(diff(c,a)).
Proof.
  (* rewrite under the diff, on the right *)
  nosimpl rewrite lem.
Abort.
