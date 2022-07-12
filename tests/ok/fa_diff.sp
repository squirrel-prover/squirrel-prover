system null.

name n : message.

global goal [set: default/left; equiv: default] _ :
  equiv(<empty,empty>,diff(n,<n,n>),empty) ->
  equiv(<empty,empty>,<diff(n,<n,n>),empty>).
Proof.
  nosimpl intro _.
  nosimpl fa <diff(n,<n,n>),_>.
  assumption.
Qed.
