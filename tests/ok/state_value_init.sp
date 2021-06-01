set autoIntro=false.

channel c

name n0: index -> index -> message
name n1: index -> message
name n2: index -> message

mutable kT(i:index,j:index): message = n0(i,j)
mutable kTbis(i:index,j:index): message = n0(j,i)

name n: index -> index -> message

process tag(i:index, j:index) =
  kT(i,j)    := n(i,j);
  kTbis(j,i) := n(i,j);
  out(c, n(i,j))

system (!_i !_j T: tag(i,j)).

goal outputAtInit:
  output@init = empty.
Proof.
auto.
Qed.

goal condAtInit:
  cond@init.
Proof.
by expand cond@init.
Qed.

goal _ (i,j:index): kT(i,j)@init = n0(i,j).
Proof.
 auto.
Qed.

goal _ (i,j:index): kTbis(i,j)@init = n0(j,i).
Proof. 
 auto.
Qed.

goal _ (k,l:index): kT(k,l)@init = n0(k,l).
Proof.
 auto.
Qed.

goal _ (k,l:index): kTbis(k,l)@init = n0(l,k).
Proof.
 auto.
Qed.
