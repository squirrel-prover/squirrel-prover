set autoIntro=false. 

name n : message
name m : message
system null.

equiv [left:default,left:default] test : diff(n,m).
Proof.
  by fresh 0.
Qed.
