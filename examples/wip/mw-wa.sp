(* Protocol MW                          *)
(* R -> T: nr                           *)
(* T -> R: nt, id + H(<c0, nr, nt>,k)   *)
(* R -> T: id + H(<c1, nr, nt>,k)       *)

hash H

abstract id: index ->message
name key:index -> message

abstract error : message
abstract ok: message
abstract ko: message

abstract tag0 : message
abstract tag1 : message
axiom tags_neq : tag0 <> tag1

channel c

process tag(i:index)=
  in(c,x);
  new nt;
  out(c,<nt,xor(id(i),H(<tag0,<x,nt>>,key(i)))>);
  in(c,y);
  if y = xor(id(i),H(<tag1, <x,nt>>,key(i))) then out(c,ok)
  else out(c,ko)

process reader =
  new nr;
  out(c,nr);
  in(c,m);
  try find i such that xor(id(i),snd(m)) = H(<tag0,<nr,fst(m)>>,key(i)) in
    out(c,xor(id(i),H(<tag1,<nr,fst(m)>>,key(i))))
  else
    out(c,error)

system (!_r R: reader | !_i !_t T: tag(i)).



goal wa_R1 :
  forall (r,i:index),
  cond@R1(r,i) =>
  exists (t:index),
  T(i,t) < R1(r,i) &&
  fst(input@R1(r,i)) = fst(output@T(i,t)) &&
  snd(input@R1(r,i)) = snd(output@T(i,t)) &&
  R(r) < T(i,t) &&
  input@T(i,t) = output@R(r).
Proof.
  intros.
  expand cond@R1(r,i).
  euf M0.
  exists t.
  assert (input@T(i,t) = nr(r)).
  fresh M2.
  depends R(r), R2(r).
  depends R(r), R1(r,i1).
Qed.


goal wa_T1 :
  forall (i,t:index),
  exec@T1(i,t) =>
  exists (r:index),
  R1(r,i) < T1(i,t) &&
  output@R1(r,i) = input@T1(i,t) &&
  T(i,t) < R1(r,i) &&
  fst(input@R1(r,i)) = fst(output@T(i,t)) &&
  snd(input@R1(r,i)) = snd(output@T(i,t)) &&
  R(r) < T(i,t) &&
  input@T(i,t) = output@R(r).
Proof.
  intros.

  assert cond@T1(i,t).
  expand exec@T1(i,t).
  expand cond@T1(i,t).
  use tags_neq.

  assert (H(<tag1,<input@T(i,t),nt(i,t)>>,key(i)) = xor(input@T1(i,t),id(i))).
  euf M2.
  exists r.
  assert R1(r,i)<T1(i,t).
    case H1.
    depends T(i,t),T1(i,t).
  nosimpl(repeat split); simpl.

  (* T < R1 *)
  assert (nt(i,t) = fst(input@R1(r,i))).
  fresh M4.
  depends T(i,t), T2(i,t).

  (* snd(input@R1) = snd(output@T) *)
  assert cond@R1(r,i).
  assert exec@R1(r,i).
  executable T1(i,t).
  use H2 with R1(r,i).
  expand exec@R1(r,i).
  expand cond@R1(r,i).

  (* R < T *)
  assert (nr(r) = input@T(i,t)).
  fresh M4.
  depends R(r), R2(r).
  depends R(r), R1(r,i1).

Qed.
