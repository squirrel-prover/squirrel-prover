hash h

abstract a : index->message
name key : index->message

abstract ok : message
abstract ko : message
abstract tagT : message
abstract tagR : message
axiom tags : tagT <> tagR

channel c

process tag(i:index) =
  in(c,nr);
  new nt;
  out(c,<a(i) XOR h(<nt,tagT>,key(i)), nt XOR h(<nr,tagR>,key(i))>)

process reader =
  new nr;
  out(c,nr);
  in(c,x);
  try find i such that xor(a(i),fst(x)) = h(<xor(h(<nr,tagR>,key(i)),snd(x)),tagT>,key(i)) in
    out(c,ok)
  else
    out(c,ko)

system ((!_k R: reader) | (!_i !_j T: tag(i))).

goal wa_fst :
  forall (k,i:index),
  cond@R1(k,i) =>
  exists j:index,
  T(i,j) < R1(k,i) &&
  fst(output@T(i,j)) = fst(input@R1(k,i)).
Proof.
  intros.
  expand cond@R1(k,i).
  euf M0.
  exists j.
  use tags.
  use tags.
Qed.

goal wa_snd :
  forall (k,i:index),
  cond@R1(k,i) =>
  exists j:index,
  T(i,j) < R1(k,i) &&
  snd(output@T(i,j)) = snd(input@R1(k,i)).
Proof.
  intros.
  expand cond@R1(k,i).
  use tags.
  euf M0.
  exists j.
  assert (xor(nt(i,j),snd(input@R1(k,i))) = h(<nr(k),tagR>,key(i))).
  euf M3.
  (* We are considering the following situation:

    R(k)->   : nR
    ->T(i,j) : ??
    ->T(i,j1): nR
    T(i,j1)->: <A+h(nT'),nT'+h(nR)>
    T(i,j)-> : <A+h(nT),nT+h(??)>
    ->R(k)   : <..,nT+h(nR)>

    The first EUF gave us that the tagT hash obtained by the reader
    must come from T(i,j).
    The second EUF tells us that the tagR hash obtained by the
    reader must come from some T(i,j1).
    But it seems hard to ensure j = j1... in fact, an artificial
    hash function satisfying EUF but not PRF would allow to
    invalidate this equality, so we cannot hope to conclude
    here without exploiting PRF somehow. *)
  admit.
Qed.
