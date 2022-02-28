(* A model of LAK with pairs but without tags.
 * It is a rare case where the authentication proof involves an induction.
 * Note that this model is unsuitable for proving unlinkability as the
 * reader action R1(j,i) reveals which tag i has been identified. *)

set postQuantumSound=true.
set autoIntro=false.

hash h

abstract ok:message
abstract ko:message

name key : index->message

channel cT
channel cR

process tag(i:index) =
  new nT;
  in(cR,nR);
  let m2 = h(<nR,nT>,key(i)) in
  out(cT,<nT,m2>);
  in(cR,m3);
  if m3 = h(<m2,nR>,key(i)) then
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

goal executable_R1 (t:timestamp) (j,i:index) :
  happens(t) => exec@t => R1(j,i)<=t => exec@R1(j,i) && cond@R1(j,i).
Proof.
  intro Hh He Hle.
  executable t => // He'.
  by use He' with R1(j,i).
Qed.

goal no_confusion :
  forall (t:timestamp,i,j,jj:index),
  t = R1(j,i) =>
  happens(R1(j,i)) => exec@R1(j,i) => R1(jj,i)<R1(j,i) =>
  <nR(j),fst(input@R1(j,i))> = <snd(input@R1(jj,i)),nR(jj)> =>
  False.
Proof.
  induction => t IH i j jj _ _ _ _ _.
  use executable_R1 with R1(j,i), jj, i as [_ _] => //.
  assert(nR(j) = h(<nR(jj),fst(input@R1(jj,i))>,key(i))) as Meq_R1jj; 1: auto.
  euf Meq_R1jj => _ _ _.

  (* EUF case 1/2: R1(j0,i)
   * We have R1(j0,i) < R1(jj,i) < R1(j,i)
   * we will appeal to to the induction hypothesis with
   * t = R1(jj,i) and jj = j0. *)
  + by use IH with R1(jj,i),i,jj,j0.

  (* EUF case 2/2: T(i,k)

     We are looking at the following situation,
     where indices i are omitted and all hashes use key(i).

     T(i,k) < R1(jj) < R1(j)

     action:     input -> output
     ----------------------------------------------------
     R(j):             -> nR(j)
     R(jj):            -> nR(jj)
     T(i,k):    nR(jj) -> <nT(i,k),h(<nR(jj),nT(i,k)>)> = M
     R1(jj):         M -> h(<h(<nR(jj)...>),nR(jj)>) = N
     R1(j): <nR(jj),N> -> ..
       executes because <h(<nR(jj),nT(i,k)>),nR(jj)> = <nR(j),nR(jj)>
       but then we have nR(j)=h(<nR(jj),nT(i,j)>) with j<>jj
       which can only happen with negligible probability. *)
  + assert (nR(j)=h(<nR(jj),nT(i,k)>,key(i))) as Hfresh; 1: auto.
    by fresh Hfresh.

Qed.

goal wa :
  forall (i:index,j:index),
  happens(R1(j,i)) => exec@R1(j,i) =>
  exists (ii:index,k:index),
  T(ii,k) <= R1(j,i) &&
  fst(input@R1(j,i)) = nT(ii,k) &&
  input@T(ii,k) = nR(j).
Proof.
  intro i j Hh He.
  rewrite /exec /cond in He; destruct He as [He Hc].
  euf Hc => _ _ _.
  (* 1/2: R1(j0,i) *)
  + use no_confusion with R1(j,i),i,j,j0 => //.
  (* 2/2: T(i,k) *)
  + by exists i,k.
Qed.
