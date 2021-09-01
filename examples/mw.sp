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
set autoIntro=false.
set timeout=4.

hash H

abstract id : index -> message
abstract id': index -> index -> message

name dummy : message

name key : index -> message
name key': index -> index -> message

abstract error : message
abstract tag0 : message
abstract tag1 : message

channel c.

process tag(i:index, t:index)=
  in(c,x);
  new nt;
  out(c,<nt,xor(diff(id(i),id'(i,t)),H(<tag0,<x,nt>>,diff(key(i),key'(i,t))))>).

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
    out(c,error).

system (!_r R: reader | !_i !_t T: tag(i,t)).

axiom len_id (i:index)   : len(id(i))    = len(dummy)
axiom len_id' (i,t:index): len(id'(i,t)) = len(dummy)

axiom tags_neq : tag0 <> tag1.

(* Well-authentication for R1's condition, formulated in an imprecise
   way with respect to the involved indices. *)
goal wa_R1 (r:index):
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
  split.

  (* Cond => WA *)
  intro [i t Meq].
  project.
  (* left *)
  euf Meq => _ _ _; 1: auto.
  exists i,t0; simpl.
  assert (input@T(i,t0) = nr(r)) as F; 1: auto.
  fresh F => C.
  by case C; 3: depends R(r), R2(r).
  (* right *)
  euf Meq => _ _ _; 1:auto.
  exists i,t; simpl.
  assert (input@T(i,t) = nr(r)) as F; 1: auto.
  fresh F => C.
  by case C; 3: depends R(r), R2(r).

  (* WA => Cond *)
  by intro [i t _]; expand output; exists i,t.
Qed.

(* Same with R2 *)
goal wa_R2 (r:index):
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
  use tags_neq; split.

  intro [i t Meq].
  project.
  (* left *)
  euf Meq => _ _ _; 1: auto.
  exists i,t0; simpl.
  assert (input@T(i,t0) = nr(r)) as F; 1: auto.
  fresh F => C.
  by case C; 2: depends R(r), R1(r).
  (* right *)
  euf Meq => _ _ _; 1:auto.
  exists i,t; simpl.
  assert (input@T(i,t) = nr(r)) as F; 1: auto.
  fresh F => C.
  by case C; 2: depends R(r), R1(r).

  (* WA => Cond *)
  by intro [i t _]; expand output; exists i,t.
Qed.

(** Same as before, but more precise wrt i, for the left process.
    There has to remain an existential quantification on t,
    because it is not involved in the condition. *)
goal [left] wa_R1_left (i,r:index):
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
  split; 2: by intro [_ _]; expand output.
  intro Meq; euf Meq => _ _ _; 1: auto.
  exists t; simpl.
  assert input@T(i,t) = nr(r) as F; 1: auto.
  fresh F => C.
  by case C; 3:depends R(r), R2(r).
Qed.

(** Precise version of wa_R1 on the right: no more existentials. *)
goal [right] wa_R1_right (i,t,r:index):
  xor(id'(i,t),snd(input@R1(r))) =
  H(<tag0,<nr(r),fst(input@R1(r))>>,key'(i,t))
  <=>
  T(i,t) < R1(r) &&
  fst(output@T(i,t)) = fst(input@R1(r)) &&
  snd(output@T(i,t)) = snd(input@R1(r)) &&
  R(r) < T(i,t) &&
  output@R(r) = input@T(i,t).
Proof.
  split; 2: by intro [_ _]; expand output.
  intro Meq; euf Meq => _ _ _; 1: auto.
  assert input@T(i,t) = nr(r) as F; 1: auto.
  fresh F => C.
  by case C; 3:depends R(r), R2(r).
Qed.

equiv unlinkability.
Proof.
induction t; try auto.

(* Case R *)
expand frame, exec, cond, output.
fa 0.
fa 1.
fa 1.
fresh 1.
yesif 1.
by (repeat split => r0 _;
    try (depends R(r0), R1(r0) by auto);
    try (depends R(r0), R2(r0) by auto)).
auto.

(* Case R1 *)
expand frame, exec, cond, output.

fa 0; fa 1.

equivalent
  (exists (i,t:index),
   diff(id(i),id'(i,t)) XOR snd(input@R1(r)) =
   H(<tag0,<nr(r),fst(input@R1(r))>>,diff(key(i),key'(i,t)))),
  (exists (i,t:index),
   T(i,t) < R1(r) &&
   fst(output@T(i,t)) = fst(input@R1(r)) &&
   snd(output@T(i,t)) = snd(input@R1(r)) &&
   R(r) < T(i,t) && output@R(r) = input@T(i,t)).
by use wa_R1 with r.

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
by intro [_ [i t _]] /=; exists i,t.
by intro [_ [i t _]] /=; exists i,t.

(* TRY-FIND *)
(* We have index variables corresponding to the existentials from
   the if-then-else condition: i,t for the honest formula and
   i1,t0 for the condition. *)
project => // [_ [i t G]].

(* LEFT *)
fa; 2: intro *; expand output; auto.
intro Meq.
use wa_R1_left with i0,r as [H1 H2].
use H1 as [_ _]; 2: expand output; auto.
by expand output; exists t.

intro *.
yesif; 1: auto.
by expand output.
auto.

(* RIGHT *)
fa; 2: intro *; expand output; auto.
intro Meq.
use wa_R1_right with i0,t0,r as [H1 H2].
use H1 as [_ _]; 2: expand output; auto.
by expand output.

intro *.
yesif; 1: auto.
by expand output.
auto.

fa 2; fadup 1.
fa 1; fadup 1.
prf 1.
ifcond 1, 1, exec@pred(R1(r)); 1: auto.
fa 1.
yesif 1.
use tags_neq; project; auto.
xor 1,n_PRF.
yesif 1.
by use len_id with i; use len_id' with i,t; namelength n_PRF, dummy.
fresh 1.
auto.

(* Case R2 *)
expand frame, exec, cond, output.

fa 0. fa 1.

equivalent
  (exists (i,t:index),
     xor(diff(id(i),id'(i,t)),snd(input@R2(r))) =
     H(<tag0,<nr(r),fst(input@R2(r))>>,diff(key(i),key'(i,t)))),
  (exists (i,t:index), T(i,t) < R2(r) &&
     fst(output@T(i,t)) = fst(input@R2(r)) &&
     snd(output@T(i,t)) = snd(input@R2(r)) &&
     R(r) < T(i,t) && output@R(r) = input@T(i,t)).
by use wa_R2 with r.

by fadup 1.

(* Case T *)
expand frame, exec, cond, output.
fa 0.
fa 1.
fa 1.
fa 1.

prf 2. (* we use PRF under XOR to be able with use XOR tactic later on *)
yesif 2.
use tags_neq.

simpl; project;
by (repeat split => > _;
    repeat split => > _ [_ [_ Meq]];
    fresh Meq).

fresh 1.
yesif 1; 1: auto.
xor 1, n_PRF.
yesif 1.
by use len_id with i; use len_id' with i,t; namelength n_PRF,dummy.
fresh 1.
auto.
Qed.
