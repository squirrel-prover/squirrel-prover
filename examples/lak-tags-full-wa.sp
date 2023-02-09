(* Full model of LAK with pairs and tags, for authentication only. *)

(* R --> T: nr                                    *)
(* T --> R: nT, h(<nR, nT, tag1>, k)              *)
(* R --> T: h(<h(<nR, nT, tag1>, k), nr, tag2>, k)*)

include Basic.
set postQuantumSound = true.

hash h

abstract ok:message
abstract ko:message

abstract tag1:message
abstract tag2:message

name key : index->message

channel cT
channel cR

process tag(i:index) =
  new nT;
  in(cR,nR);
  out(cT,<nT,h(<<nR,nT>,tag1>,key(i))>);
  in(cR,m3);
  if m3 = h(<<h(<<nR,nT>,tag1>,key(i)),nR>,tag2>,key(i)) then
    out(cT,ok)
  else
    out(cT,ko)

process reader =
  new nR;
  out(cR,nR);
  in(cT,x);
  try find i such that snd(x) = h(<<nR,fst(x)>,tag1>,key(i)) in
    out(cR,h(<<snd(x),nR>,tag2>,key(i)))
  else
    out(cR,ko)

system ((!_k R: reader) | (!_i !_j T: tag(i))).

axiom tags_neq : tag1 <> tag2.

goal wa_R (k,i:index[param]):
  happens(R1(k,i)) =>
  cond@R1(k,i) =>
  exists (j:index),
  T(i,j) < R1(k,i) &&
  fst(input@R1(k,i)) = fst(output@T(i,j)) &&
  snd(input@R1(k,i)) = snd(output@T(i,j)) &&
  R(k) < T(i,j) &&
  output@R(k) = input@T(i,j).
Proof.
  intro _ Hc.
  rewrite /cond in Hc. 
  euf Hc => // [l [_ _]].
  + by use tags_neq.
  + exists l.
    assert (nR(k) = input@T(i,l)) as Mfresh by auto.
    fresh Mfresh; intro Hfresh; try destruct Hfresh as [i' Hfresh].
    - auto.
    - by depends R(k), R1(k,i').
    - by depends R(k), R2(k).
  + exists l.
    assert (nR(k) = input@T(i,l)) as Mfresh by auto.
    depends T(i,l), T1(i,l); [1:auto | 2:intro _].
    fresh Mfresh; intro Hfresh; try destruct Hfresh as [i' Hfresh].
    - auto.
    - by depends R(k), R1(k,i').
    - by depends R(k), R2(k).
  + exists l.
    assert (nR(k) = input@T(i,l)) as Mfresh by auto.
    depends T(i,l), T2(i,l); [1:auto | 2:intro _].
    fresh Mfresh; intro Hfresh; try destruct Hfresh as [i' Hfresh].
    - auto.
    - by depends R(k), R1(k,i').
    - by depends R(k), R2(k).
Qed.

goal executable_R1 (t:timestamp) (k,i:index) :
  happens(t) => exec@t => R1(k,i)<=t => exec@R1(k,i) && cond@R1(k,i).
Proof.
  intro _ _ _.
  executable t => // He.
  by use He with R1(k,i).
Qed.

goal wa_T (i,j:index[param]):
  happens(T1(i,j)) =>
  exec@T1(i,j) =>

  exists (k:index),
  R1(k,i) < T1(i,j) &&
  output@R1(k,i) = input@T1(i,j) &&
  T(i,j) < R1(k,i) &&
  fst(output@T(i,j)) = fst(input@R1(k,i)) &&
  snd(output@T(i,j)) = snd(input@R1(k,i)) &&
  R(k) < T(i,j) &&
  output@R(k) = input@T(i,j).

Proof.
  intro Hh He.
  assert cond@T1(i,j) as Hc by auto.
  use tags_neq as _.
  rewrite /cond in Hc; euf Hc => // [k [H1t H1m]]. 
  assert (snd(input@R1(k,i)) = h(<<input@T(i,j),nT(i,j)>,tag1>,key(i)))
    as Heuf by auto.
  euf Heuf => // [l [H2t H2m]];
  assert (nT(i,j)=nT(i,l)) as Hf; [1: auto | 2:fresh Hf; intro _].
  * case H1t; case H2t; try auto.
    exists k.
    use executable_R1 with T1(i,j),k,i as [He' Hc'] => //.
    assert h(<<nR(k),fst(input@R1(k,i))>,tag1>,key(i)) =
         h(<<input@T(i,j),nT(i,j)>,tag1>,key(i))
      as Hcoll by auto.
    collision Hcoll => Hcoll'.
    assert (input@T(i,j) = nR(k)) as Hfresh by auto.
    fresh Hfresh; intro Hfresh'; try destruct Hfresh' as [i0 Hfresh'].
    + auto.
    + by depends R(k), R1(k,i0).
    + by depends R(k), R2(k).
  * depends T(i,j), T1(i,j); [1:auto | 2:intro _].
   case H1t; case H2t; try auto.
  * case H1t; case H2t; depends T(i,j), T2(i,j); try auto.
    intro _; assert T2(i,j) < T1(i,j); [1:auto].
    use mutex_default_T1_T2 with i,j. by case H.
Qed.

