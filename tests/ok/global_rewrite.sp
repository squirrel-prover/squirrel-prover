abstract a : message
abstract b : message.

system null.

axiom [any] refl (x:message) : x = x.

global goal _ : [a=b] -> [b=a].
Proof.
  nosimpl intro G.
  nosimpl rewrite G.
  nosimpl apply refl.
Qed.
