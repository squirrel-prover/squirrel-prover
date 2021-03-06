hash h

abstract ok:message
abstract ko:message

name key : index->message

channel cT
channel cR

(* This should be builtin and automatic: TODO. *)
axiom happens_le :
  forall (t:timestamp,tt:timestamp),
  t <= tt && t <> init && happens(tt) => happens(t)

process tag(i:index) =
  new nT;
  in(cR,nR);
  let m2 = h(<nR,nT>,key(i)) in
  out(cT,<nT,m2>);
  in(cR,m3);
  if m3@nT = h(<m2,nR>,key(i)) then
    out(cT,ok)
  else
    out(cT,ko)

process reader(j:index) =
  new nR;
  out(cR,nR);
  in(cT,x);
  try find i such that snd(x) = h(<nR,fst(x)>,key(i)) in
    out(cR,h(<snd(x),nR>,key(i)))
  else
    out(cR,ko)

system ((!_j R: reader(j)) | (!_i !_k T: tag(i))).

goal no_confusion :
  forall (t:timestamp,i:index,j:index,jj:index),
  t = R1(j,i) =>
  happens(R1(jj,i)) => happens(R1(j,i)) => R1(jj,i)<R1(j,i) =>
  <nR(j),fst(input@R1(j,i))> = <snd(input@R1(jj,i)),nR(jj)> =>
  False.
Proof.
  nosimpl(induction).
  nosimpl(intros).
  (* TODO without these nosimpl some message equalities are introduced;
   *  they are consequences of t=R1(j,i), I don't know which tactic
   *  puts them in, and I don't want them. *)
  assert(nR(j) = h(<nR(jj),fst(input@R1(jj,i))>,key(i))).
  euf M1.
  cycle 1.
  (* We are looking at this situation (all hashes use key(i)):
     R(j):          -> nR(j)
     R(jj):         -> nR(jj)
     T(i,k): nR(jj) -> <nT(i,k),h(<nR(jj),nT(i,k)>)> = M
     R1(jj,i):    M -> h(<h(<nR(jj)...>),nR(jj)>) = N
     R1(j,i): <nR(jj),N> -> ..
       executes because <h(<nR(jj),nT(i,k)>),nR(jj)> = <nR(j),nR(jj)>
       but then we have nR(j)=h(<nR(jj),nT(i,j)>) with j<>jj
       which can only happen with negligible probability. *)
  assert (nR(j)=h(<nR(jj),nT(i,k)>,key(i))).
  case H0.

  (* Now we have R1(j1,i) < R1(jj,i) < R1(j,i)
   * we will appeal to to the induction hypothesis with
   * t = R1(jj,i) and jj = j1. *)
  use IH0 with R1(jj,i),i,jj,j1.

  use happens_le with R1(j1,i), R1(jj,i).

Qed.

goal wa :
  forall (i:index,j:index),
  happens(R1(j,i)) =>
  exists (ii:index,k:index),
  T(ii,k) <= R1(j,i) &&
  fst(input@R1(j,i)) = nT(ii,k) &&
  input@T(ii,k) = nR(j).
Proof.
  intros.
  euf C0.
  use no_confusion with R1(j,i),i,j,j1.
  use happens_le with R1(j1,i), R1(j,i).
  exists i,k.
Qed.
