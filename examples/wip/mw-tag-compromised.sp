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

In this model, we add a compromised tag (id0,key0 for the left process,
id0',key0' for the right process).
This compromised tag cannot play (no process tag(i,t) with these credentials)
but these credentials are in the reader's database.
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

(* Ideally, we would like to write something like "abstract i0 : index"
to model a compromised tag, but it is not (yet?) allowed by the parser.
A possible bypass is the following declarations and axiom, but we actually
write something that is incorrect.
For example, id(ii) is a name whereas id0 is a message, so there is a
negligible probability that id(ii) and id0 are equal. *)
abstract id0 : message
abstract id0' : message
abstract key0 : message
abstract key0' : message
axiom compromisedCredentials :
  exists (ii,ii':index),
    id(ii) = id0 && key(ii) = key0 && id'(ii,ii') = id0' && key'(ii,ii') = key0'
    && (forall (tau:timestamp), forall (i,t:index), tau = T(i,t) => i <> ii)

system [compromised] null.

(* Well-authentication for R1's condition, formulated in an imprecise
   way with respect to the involved indices. *)
goal wa_R1 : forall r:index,
  (exists (i,t:index), id(i) <> id0 && key(i) <> key0 && id'(i,t) <> id0' && key'(i,t) <> key0' &&
   xor(diff(id(i),id'(i,t)),snd(input@R1(r))) =
   H(<tag0,<nr(r),fst(input@R1(r))>>,diff(key(i),key'(i,t))))
  <=>
  (exists (i,t:index), id(i) <> id0 && key(i) <> key0 && id'(i,t) <> id0' && key'(i,t) <> key0' &&
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
  euf M4.
  exists i,t1.
  assert (input@T(i,t1) = nr(r)).
  fresh M6.
  use compromisedCredentials.
  depends R(r), R2(r).
  use compromisedCredentials.
  (* right *)
  euf M4.
  exists i,t.
  assert (input@T(i,t) = nr(r)).
  fresh M6.
  depends R(r), R2(r).

  (* WA => Cond *)
  exists i,t.

Qed.

(* Same with R2 *)
goal wa_R2 : forall r:index,
  (exists (i,t:index), id(i) <> id0 && key(i) <> key0 && id'(i,t) <> id0' && key'(i,t) <> key0' &&
   xor(diff(id(i),id'(i,t)),snd(input@R2(r))) =
   H(<tag0,<nr(r),fst(input@R2(r))>>,diff(key(i),key'(i,t))))
  <=>
  (exists (i,t:index), id(i) <> id0 && key(i) <> key0 && id'(i,t) <> id0' && key'(i,t) <> key0' &&
   T(i,t) < R2(r) &&
   fst(output@T(i,t)) = fst(input@R2(r)) &&
   snd(output@T(i,t)) = snd(input@R2(r)) &&
   R(r) < T(i,t) &&
   output@R(r) = input@T(i,t)).
Proof.

  use tags_neq; split.

  (* Cond => WA *)
  project.
  (* left *)
  euf M5.
  exists i,t1.
  assert (input@T(i,t1) = nr(r)).
  fresh M7.
  use compromisedCredentials.
  depends R(r), R1(r).
  use compromisedCredentials.
  (* right *)
  euf M5.
  exists i,t.
  assert (input@T(i,t) = nr(r)).
  fresh M7.
  depends R(r), R1(r).

  (* WA => Cond *)
  exists i,t.

Qed.

(** Same as before, but more precise wrt i, for the left process.
    There has to remain an existential quantification on t,
    because it is not involved in the condition. *)
goal [left] wa_R1_left : forall (i,r:index),
  (id(i) <> id0 && key(i) <> key0)
  =>
  (xor(id(i),snd(input@R1(r))) =
  H(<tag0,<nr(r),fst(input@R1(r))>>,key(i))
  <=>
  exists t:index, id'(i,t) <> id0' && key'(i,t) <> key0' &&
  T(i,t) < R1(r) &&
  fst(output@T(i,t)) = fst(input@R1(r)) &&
  snd(output@T(i,t)) = snd(input@R1(r)) &&
  R(r) < T(i,t) &&
  output@R(r) = input@T(i,t)).
Proof.
  intros.
  euf M2.
  exists t.
  assert input@T(i,t) = nr(r).
  fresh M4.
  use compromisedCredentials.
  depends R(r), R2(r).
  use compromisedCredentials.
Qed.

(** Precise version of wa_R1 on the right: no more existentials. *)
goal [right] wa_R1_right : forall (i,t,r:index),
  (id(i) <> id0 && key(i) <> key0 && key'(i,t) <> key0')
  =>
  (xor(id'(i,t),snd(input@R1(r))) =
  H(<tag0,<nr(r),fst(input@R1(r))>>,key'(i,t))
  <=>
  T(i,t) < R1(r) &&
  fst(output@T(i,t)) = fst(input@R1(r)) &&
  snd(output@T(i,t)) = snd(input@R1(r)) &&
  R(r) < T(i,t) &&
  output@R(r) = input@T(i,t)).
Proof.
  intros.
  euf M3.
  assert input@T(i,t) = nr(r).
  fresh M5.
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
split.
use compromisedCredentials.
use wa_R1 with r.
use compromisedCredentials.
use wa_R1 with r.

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
use compromisedCredentials.
false_left.
use wa_R1_left with i,r.
use H1.
yesif.
use compromisedCredentials.
fa.
use compromisedCredentials.
use wa_R1_right with i,t,r.
use H1.
yesif.
use compromisedCredentials.

fa 2. fadup 1.
fa 1. fadup 1.
prf 1.
ifcond 1, 1, exec@pred(R1(r)).
fa 1.
yesif 1.
use tags_neq; project.
xor 1,n_PRF.
yesif 1.
use len_id to i; use len_id' with i,t; namelength n_PRF, dummy.

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
split.
use compromisedCredentials.
false_left.
use wa_R2 with r.
exists i,t.

fadup 1.

(* Case T *)
expand frame@T(i,t); expand exec@T(i,t).
expand cond@T(i,t);expand output@T(i,t).
fa 0.
fa 1.
fa 1.
fa 1.

prf 2. (* we use PRF under XOR to be able with use XOR tactic later on *)
yesif 2.
use tags_neq.
project.
assert (fst(input@R1(r)) = nt(i,t)).
fresh M2.
assert (fst(input@R1(r)) = nt(i,t)).
fresh M2.
fresh 1. yesif 1.
xor 1, n_PRF1.
yesif 1.
use len_id to i; use len_id' with i,t; namelength n_PRF1,dummy.
Qed.
