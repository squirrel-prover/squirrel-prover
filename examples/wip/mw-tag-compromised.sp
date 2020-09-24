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
*******************************************************************************)

hash H

abstract id : index -> message
abstract id': index -> index -> message

name dummy : message
axiom len_id : forall (i:index), len(id(i)) = len(dummy)
axiom len_id' : forall (i,t:index), len(id'(i,t)) = len(dummy)

name key : index -> message
name key': index -> index -> message

abstract error : message
abstract tag0 : message
abstract tag1 : message
axiom tags_neq : tag0 <> tag1

channel c

abstract id0 : message
abstract id0' : message
abstract key0 : message
abstract key0' : message
axiom compromisedCredentials :
  exists (i0,i0':index), 
    id(i0) = id0 && key(i0) = key0 && id'(i0,i0') = id0' && key'(i0,i0') = key0'

process tag(i:index, t:index)=
  in(c,x);
  new nt;
  out(c,<nt,xor(diff(id(i),id'(i,t)),H(<tag0,<x,nt>>,diff(key(i),key'(i,t))))>)

process reader =
  new nr;
  out(c,nr);
  in(c,m);
  if exists (i,t:index),
     xor(diff(id(i),id'(i,t)),snd(m)) =
     H(<tag0,<nr,fst(m)>>,diff(key(i),key'(i,t)))
  then
    out(c, try find i,t such that
             xor(diff(id(i),id'(i,t)),snd(m)) = H(<tag0,<nr,fst(m)>>,diff(key(i),key'(i,t))) in
           xor(diff(id(i),id'(i,t)),H(<tag1,<nr,fst(m)>>,diff(key(i),key'(i,t)))))
  else
    out(c,error)

system (!_r R: reader | !_i !_t T: tag(i,t)).


(* Well-authentication for R1's condition, formulated in an imprecise
   way with respect to the involved indices. *)
goal wa_R1 : forall r:index,
  (exists (i,t:index),
   xor(diff(id(i),id'(i,t)),snd(input@R1(r))) =
   H(<tag0,<nr(r),fst(input@R1(r))>>,diff(key(i),key'(i,t))))
  <=>
  (exists (i,t:index),
   T(i,t) < R1(r) &&
   fst(output@T(i,t)) = fst(input@R1(r)) &&
   snd(output@T(i,t)) = snd(input@R1(r)) &&
   R(r) < T(i,t) &&
   output@R(r) = input@T(i,t)).
Proof.
  intros; split.

  (* Cond => WA *)
  project.
  (* left *)
  euf M0.
  exists i,t1.
  assert (input@T(i,t1) = nr(r)).
  fresh M2.
  depends R(r), R2(r).
  (* right *)
  euf M0.
  exists i,t.
  assert (input@T(i,t) = nr(r)).
  fresh M2.
  depends R(r), R2(r).

  (* WA => Cond *)
  exists i,t.

Qed.

(* Same with R2 *)
goal wa_R2 : forall r:index,
  (exists (i,t:index),
   xor(diff(id(i),id'(i,t)),snd(input@R2(r))) =
   H(<tag0,<nr(r),fst(input@R2(r))>>,diff(key(i),key'(i,t))))
  <=>
  (exists (i,t:index),
   T(i,t) < R2(r) &&
   fst(output@T(i,t)) = fst(input@R2(r)) &&
   snd(output@T(i,t)) = snd(input@R2(r)) &&
   R(r) < T(i,t) &&
   output@R(r) = input@T(i,t)).
Proof.

  apply tags_neq; split.

  (* Cond => WA *)
  project.
  (* left *)
  euf M1.
  exists i,t1.
  assert (input@T(i,t1) = nr(r)).
  fresh M3.
  depends R(r), R1(r).
  (* right *)
  euf M1.
  exists i,t.
  assert (input@T(i,t) = nr(r)).
  fresh M3.
  depends R(r), R1(r).

  (* WA => Cond *)
  exists i,t.

Qed.

(** Same as before, but more precise wrt i, for the left process.
    There has to remain an existential quantification on t,
    because it is not involved in the condition. *)
goal [left] wa_R1_left : forall (i,r:index),
  xor(id(i),snd(input@R1(r))) =
  H(<tag0,<nr(r),fst(input@R1(r))>>,key(i))
  <=>
  exists t:index,
  T(i,t) < R1(r) &&
  fst(output@T(i,t)) = fst(input@R1(r)) &&
  snd(output@T(i,t)) = snd(input@R1(r)) &&
  R(r) < T(i,t) &&
  output@R(r) = input@T(i,t).
Proof.
  intros.
  euf M0.
  exists t.
  assert input@T(i,t) = nr(r).
  fresh M2.
  depends R(r), R2(r).
Qed.

(** Precise version of wa_R1 on the right: no more existentials. *)
goal [right] wa_R1_right : forall (i,t,r:index),
  xor(id'(i,t),snd(input@R1(r))) =
  H(<tag0,<nr(r),fst(input@R1(r))>>,key'(i,t))
  <=>
  T(i,t) < R1(r) &&
  fst(output@T(i,t)) = fst(input@R1(r)) &&
  snd(output@T(i,t)) = snd(input@R1(r)) &&
  R(r) < T(i,t) &&
  output@R(r) = input@T(i,t).
Proof.
  intros.
  euf M0.
  assert input@T(i,t) = nr(r).
  fresh M2.
  depends R(r), R2(r).
Qed.


equiv unlinkability.
Proof.
induction t.

(* Case R *)
expand frame@R(r); expand exec@R(r).
expand cond@R(r);expand output@R(r).
fa 0.
fa 1.
fa 1.
fresh 1.
yesif 1.
repeat split.
depends R(r1), R2(r1).
depends R(r1), R1(r1).

(* Case R1 *)
expand frame@R1(r); expand exec@R1(r).
expand cond@R1(r); expand output@R1(r).

fa 0. fa 1.

equivalent
  (exists (i,t:index),
   diff(id(i),id'(i,t)) XOR snd(input@R1(r)) =
   H(<tag0,<nr(r),fst(input@R1(r))>>,diff(key(i),key'(i,t)))),
  (exists (i,t:index),
   T(i,t) < R1(r) &&
   fst(output@T(i,t)) = fst(input@R1(r)) &&
   snd(output@T(i,t)) = snd(input@R1(r)) &&
   R(r) < T(i,t) && output@R(r) = input@T(i,t)).
apply wa_R1 to r.

(* Perform a similar rewriting in try-find condition,
   also propagating exec@pred(R1(r)) there, and changing
   fst(input@R1(r)) into nt(i,t) in the final output. *)
equivalent
  (if exec@pred(R1(r)) &&
      exists (i,t:index),
      T(i,t) < R1(r) &&
      fst(output@T(i,t)) = fst(input@R1(r)) &&
      snd(output@T(i,t)) = snd(input@R1(r)) &&
      R(r) < T(i,t) && output@R(r) = input@T(i,t)
   then try find i,t such that
      xor(diff(id(i),id'(i,t)),snd(input@R1(r))) =
      H(<tag0,<nr(r),fst(input@R1(r))>>,diff(key(i),key'(i,t)))
   in
      diff(id(i),id'(i,t)) XOR
      H(<tag1,<nr(r),fst(input@R1(r))>>,diff(key(i),key'(i,t)))),
  (if exec@pred(R1(r)) &&
      exists (i,t:index),
      T(i,t) < R1(r) &&
      fst(output@T(i,t)) = fst(input@R1(r)) &&
      snd(output@T(i,t)) = snd(input@R1(r)) &&
      R(r) < T(i,t) && output@R(r) = input@T(i,t)
   then
   try find i,t such that
      exec@pred(R1(r)) &&
      (T(i,t) < R1(r) &&
       fst(output@T(i,t)) = fst(input@R1(r)) &&
       snd(output@T(i,t)) = snd(input@R1(r)) &&
       R(r) < T(i,t) && output@R(r) = input@T(i,t))
   in
   if exec@pred(R1(r)) then
      diff(id(i),id'(i,t)) XOR
      H(<tag1,<nr(r),nt(i,t)>>,diff(key(i),key'(i,t)))).

(* IF-THEN-ELSE *)
nosimpl(fa); try auto.
nosimpl(intro); split; assumption.
nosimpl(intro); split; assumption.

(* TRY-FIND *)
(* We have index variables corresponding to the existentials from
   the if-then-else condition: i,t for the honest formula and
   i1,t1 for the condition. *)
project.
fa.
apply wa_R1_left to i1,r.
apply H1.
exists t.
yesif.
fa.
apply wa_R1_right to i1,t1,r.
apply H1.
yesif.

fa 2. fadup 1.
fa 1. fadup 1.
prf 1.
ifcond 1, 1, exec@pred(R1(r)).
fa 1.
yesif 1.
apply tags_neq; project.
xor 1,n_PRF.
yesif 1.
apply len_id to i; apply len_id' to i,t; namelength n_PRF, dummy.

(* Case R2 *)
expand frame@R2(r); expand exec@R2(r).
expand cond@R2(r); expand output@R2(r).

fa 0. fa 1.

equivalent
  (exists (i,t:index),
     xor(diff(id(i),id'(i,t)),snd(input@R2(r))) =
     H(<tag0,<nr(r),fst(input@R2(r))>>,diff(key(i),key'(i,t)))),
  (exists (i,t:index), T(i,t) < R2(r) &&
     fst(output@T(i,t)) = fst(input@R2(r)) &&
     snd(output@T(i,t)) = snd(input@R2(r)) &&
     R(r) < T(i,t) && output@R(r) = input@T(i,t)).
apply wa_R2 to r.

fadup 1.

(* Case T *)
expand frame@T(i,t); expand exec@T(i,t).
expand cond@T(i,t);expand output@T(i,t).
fa 0.
fa 1.
fa 1.
fa 1.

prf 2. (* we apply PRF under XOR to be able to use XOR tactic later on *)
yesif 2.
apply tags_neq.
project.
assert (fst(input@R1(r)) = nt(i,t)).
fresh M2.
assert (fst(input@R1(r)) = nt(i,t)).
fresh M2.
fresh 1. yesif 1.
xor 1, n_PRF1.
yesif 1.
apply len_id to i; apply len_id' to i,t; namelength n_PRF1,dummy.
Qed.
