hash H

abstract ok : message
abstract error : message

name key : index -> message

channel c

process tag(i,j:index) =
  new n; out(c, <n, H(n,key(i))>)

process reader(j:index) =
  in(c,x);
  try find i such that snd(x) = H(fst(x), key(i))
  in out(c,ok)
  else out(c,error)

system (!_j R: reader(j) | !_i !_j T: tag(i,j)).


goal auth (i:index, j:index):
  happens(R(j,i)) =>
  cond@R(j,i) =>
  exists (j':index), T(i,j') < R(j,i) &&
  fst(input@R(j,i)) = fst(output@T(i,j')) &&
  snd(input@R(j,i)) = snd(output@T(i,j')).
Proof.
  intro Hap Hcond.
  expand cond.
  euf Hcond.
  intro [j0 _]. by exists j0.
Qed.
