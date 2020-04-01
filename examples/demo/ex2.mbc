hash h

abstract ok:message
abstract ko:message

name key : index->message

channel cT
channel cR

process tag(i:index) =
  new nT;
  T : out(cT, <nT, h(nT,key(i))>)

process reader(j:index) =
  in(cT,x);
  try find i such that snd(x) = h(fst(x),key(i)) in
    R: out(cR,ok)
  else
    R1 : out(cR,ko)

system ((!_j reader(j)) | (!_i !_k tag(i))).

(* Authentication goal *)
goal wa :
  forall (i:index, j:index),
     cond@R(j,i) =>
         exists (k:index),
              T(i,k) <= R(j,i) && fst(input@R(j,i)) = nT(i,k).
Proof.
  ????
Qed.
