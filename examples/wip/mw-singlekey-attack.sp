(*******************************************************************************
MW

[E] David Molnar and David A. Wagner. Privacy and security in library
RFID: issues, practices, and architectures. In Vijayalakshmi Atluri,
Birgit Pfitzmann, and Patrick D. McDaniel, editors, Proceedings of the
11th ACM Conference on Computer and Communications Security, CCS
2004, Washington, DC, USA, October 25-29, 2004, pages 210–219.
ACM, 2004.

R --> T: nr
T --> R: nt, id + H(<c0, nr, nt>,k)
R --> T: id + H(<c1, nr, nt>,k)

This is a "light" model without the last check of T.

/!\ In this version, all tags share the same key. The goal is to prove that
well-authentication does not hold.
*******************************************************************************)

hash H

abstract id : index -> message

name dummy : message
axiom len_id : forall (i:index) len(id(i)) = len(dummy)

name key : message

abstract error : message
abstract tag0 : message
abstract tag1 : message
axiom tags_neq : tag0 <> tag1

channel c

process tag(i:index, t:index)=
  in(c,x);
  new nt;
  out(c,<nt,xor(id(i),H(<tag0,<x,nt>>,key))>)

process reader =
  new nr;
  out(c,nr);
  in(c,m);
  if exists (i:index),
     xor(id(i),snd(m)) =
     H(<tag0,<nr,fst(m)>>,key)
  then
    out(c, try find i such that
             xor(id(i),snd(m)) = H(<tag0,<nr,fst(m)>>,key) in
           xor(id(i),H(<tag1,<nr,fst(m)>>,key)))
  else
    out(c,error)

system (!_r R: reader | !_i !_t T: tag(i,t)).


goal not_wa_R1 : forall (i,r:index),
  xor(id(i),snd(input@R1(r))) =
  H(<tag0,<nr(r),fst(input@R1(r))>>,key)
  =>
  ((exists t:index, (* honest case *)
  T(i,t) < R1(r) &&
  fst(output@T(i,t)) = fst(input@R1(r)) &&
  snd(output@T(i,t)) = snd(input@R1(r)) &&
  R(r) < T(i,t) &&
  output@R(r) = input@T(i,t))
  ||
  (exists (i1,t:index), (* dishonest case *)
  i1 <> i &&
  T(i1,t) < R1(r) &&
  fst(output@T(i1,t)) = fst(input@R1(r)) &&
  snd(output@T(i1,t)) XOR id(i) XOR id(i1) = snd(input@R1(r)) &&
  R(r) < T(i1,t) &&
  output@R(r) = input@T(i1,t))).
Proof.
  intros.
  euf M0.

  assert (i1 <> i || i = i1).
  case H0.

(* case i1 <> i : dishonest interaction *)
  right.
  exists i1,t.
  assert input@T(i1,t) = nr(r).
  fresh M2.
  depends R(r), R2(r).

(* case i1 = i : honest interaction *)
  left.
  exists t.
  assert input@T(i,t) = nr(r).
  fresh M2.
  depends R(r), R2(r).
Qed.



goal not_wa_R1_merge : forall (i,r:index),
  xor(id(i),snd(input@R1(r))) =
  H(<tag0,<nr(r),fst(input@R1(r))>>,key)
  =>
  (exists (i1,t:index),
    (* we might have i=i1 (honest) or not (dishonest) *)
  T(i1,t) < R1(r) &&
  fst(output@T(i1,t)) = fst(input@R1(r)) &&
  snd(output@T(i1,t)) XOR id(i) XOR id(i1) = snd(input@R1(r)) &&
  R(r) < T(i1,t) &&
  output@R(r) = input@T(i1,t)).
Proof.
  intros.
  euf M0.
  exists i1,t.
  assert input@T(i1,t) = nr(r).
  fresh M2.
  depends R(r), R2(r).
Qed.
