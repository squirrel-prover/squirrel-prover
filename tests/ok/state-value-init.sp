channel c

name n0: index -> index -> message

mutable kT(i:index,j:index): message = n0(i,j)

name n: index -> index -> message

process tag(i:index, j:index) =
  kT(i,j) := n(i,j);
  out(c, n(i,j))

system (!_i !_j T: tag(i,j)).

goal outputAtInit:
  output@init = empty.
Proof.
simpl.
Qed.
