include Core.

hash h
abstract ok : message
abstract ko : message.

name key  : index -> message

channel cT
channel cR.

process tag(i:index,k:index) =
  new nT; out(cT, <nT, h(nT,key(i))>).

process reader(j:index) =
  in(cT,x);
  if exists (i:index), snd(x) = h(fst(x),key(i)) then R1: out(cR,ok)
  else R2: out(cR,ko).


system BasicHash =  ((!_j R: reader(j)) | (!_i !_k T: tag(i,k))).

lemma [BasicHash] authentication :
 forall (j:index), happens(R1(j)) =>
                   cond@R1(j) =>
                   (exists (i,k:index), T(i,k) < R1(j)
                              && fst(output@T(i,k)) = fst(input@R1(j))
                              && snd(output@T(i,k)) = snd(input@R1(j))).
Proof.
intro j Hap Hcond.
expand cond@R1(j).
destruct Hcond as [i0 HEq].
euf HEq.
intro [k0 [HOrd Eq]].
by exists i0, k0.
Qed.


