system null.

name n1 : message
name n2 : message
name m1 : message
name m2 : message

global axiom [default] ax : equiv(diff(n1,m1),diff(n2,m2)).
axiom [default/right] ax1 : m1 = empty.
axiom [default/right] ax2 : m2 = empty.

goal [default/left,default/left] _ : diff(n1,n2) = empty.
Proof.
  rewrite equiv ax.
  project.
  + apply ax1.
  + apply ax2.
Qed.
