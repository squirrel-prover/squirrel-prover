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

This is a "full" model with the last check of T, but our tool lacks a notion of
induction over sequences to complete the proof.
*******************************************************************************)

hash H

abstract id : index->message
abstract id': index->index->message

name key : index->message
name key': index->index->message

abstract ok : message
abstract ko : message
abstract error : message
abstract tag0 : message
abstract tag1 : message

channel c

process tag(i:index, t:index)=
  in(c,x);
  new nt;
  out(c,<nt,xor(diff(id(i),id'(i,t)),H(<tag0,<x,nt>>,diff(key(i),key'(i,t))))>);
  in(c,y);
  if y = xor(diff(id(i),id'(i,t)),H(<tag1,<x,nt>>,diff(key(i),key'(i,t)))) 
  then out(c,ok)
  else out(c,ko)

process reader =
  new nr;
  out(c,nr);
  in(c,m);
  if exists (i,t:index),
     xor(diff(id(i),id'(i,t)),snd(m)) =
     H(<tag0,<nr,fst(m)>>,diff(key(i),key'(i,t)))
  then
    out(c, try find i,t such that
             xor(diff(id(i),id'(i,t)),snd(m)) =
             H(<tag0,<nr,fst(m)>>,diff(key(i),key'(i,t)))
           in
             xor(diff(id(i),id'(i,t)),
                 H(<tag1,<nr,fst(m)>>,diff(key(i),key'(i,t)))))
  else
    out(c,error)

system (!_r R: reader | !_i !_t T: tag(i,t)).

axiom tags_neq : tag0 <> tag1.

(* Well-authentication for R1's condition, formulated in an imprecise
   way with respect to the involved indices. *)
goal wa_R1 : forall r:index,
  (exists (i,t:index),
   xor(diff(id(i),id'(i,t)),snd(input@R1(r))) =
   H(<tag0,<nr(r),fst(input@R1(r))>>,diff(key(i),key'(i,t))))
  <=>
  (exists (i,t:index),
   T(i,t) < R1(r) &&
   snd(output@T(i,t)) = snd(input@R1(r)) &&
   fst(output@T(i,t)) = fst(input@R1(r)) &&
   R(r) < T(i,t) &&
   output@R(r) = input@T(i,t)).
Proof.

  intro *; split.

  (* Cond => WA *)
  project.
  (* left *)
  euf Meq.
  exists i,t1.
  assert (input@T(i,t1) = nr(r)).
  fresh Meq1.
  by case H; depends R(r), R2(r).
  (* right *)
  euf Meq.
  exists i,t.
  assert (input@T(i,t) = nr(r)).
  fresh Meq1.
  by case H; depends R(r), R2(r).

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
  snd(output@T(i,t)) = snd(input@R1(r)) &&
  fst(output@T(i,t)) = fst(input@R1(r)) &&
  R(r) < T(i,t) &&
  output@R(r) = input@T(i,t).
Proof.
  intro *.
  euf Meq.
  exists t.
  assert input@T(i,t) = nr(r).
  fresh Meq1.
  by case H; depends R(r), R2(r).
Qed.

(** Precise version of wa_R1 on the right: no more existentials. *)
goal [right] wa_R1_right : forall (i,t,r:index),
  xor(id'(i,t),snd(input@R1(r))) =
  H(<tag0,<nr(r),fst(input@R1(r))>>,key'(i,t))
  <=>
  T(i,t) < R1(r) &&
  snd(output@T(i,t)) = snd(input@R1(r)) &&
  fst(output@T(i,t)) = fst(input@R1(r)) &&
  R(r) < T(i,t) &&
  output@R(r) = input@T(i,t).
Proof.
  intro *.
  euf Meq.
  assert input@T(i,t) = nr(r).
  fresh Meq1.
  by case H; depends R(r), R2(r).
Qed.

equiv unlinkability.
Proof.

(* Before starting the proof by induction we enrich the biframe.
   The following sequences over-approximate the messages that the
   attacker may learn during protocol executions. Note that the
   hashes using tag0 contain an arbitrary input@T(i,t) because
   no authentication can be guaranteed at this point, while
   hashes using tag1 contain a fixed message <nr(r),nt(i,t)>
   since past execution conditions can guarantee that only
   this content can be hashed.

   Due to the addition of these sequences the cases where tau is
   some action of the protocol are eased (we can use dup) and some
   of the difficulty is moved to the base case (tau = init).
   The biframe in that base case only contains these sequences.

   We cannot formally prove the indistinguishability of the biframe
   in that base case, because we lack a notion of induction on sequences.
   However, the essence of the proof is simple:
   - we can get rid of tag1 hashes using prf and fresh
     because these hashed messages are distinct from the tag0 messages
     by tags_neq, and pairwise distinct thanks to the nonces nr(r) and
     nt(i,t);
   - we can then get rid of tag0 hashes using prf and fresh
     because the nonce nt(i,t) guarantees that the hashed messages
     are pairwise distinct;
   - we can finally get rid of the nonces nr and nt in the first
     two sequences using fresh. *)

enrich seq(r -> nr(r)).
enrich seq(i,t -> nt(i,t)).
enrich seq(i,t -> diff(id(i),id'(i,t)) XOR
                  H(<tag0,<input@T(i,t),nt(i,t)>>,diff(key(i),key'(i,t)))).
enrich seq(i,r,t -> diff(id(i),id'(i,t)) XOR
                    H(<tag1,<nr(r),nt(i,t)>>,diff(key(i),key'(i,t)))).
induction t.

(* Init case *)
by admit. (* see comment above *)

(* Case R - Done *)
expand frame@R(r). fa 4.
by expand seq(r->nr(r)), r.

(* Case R1  WIP *)
expand frame@R1(r); expand exec@R1(r).
expand cond@R1(r); expand output@R1(r).
fa 4; fa 5.

equivalent
  (exists (i,t:index), xor(diff(id(i),id'(i,t)),snd(input@R1(r))) =
                       H(<tag0,<nr(r),fst(input@R1(r))>>,diff(key(i),key'(i,t)))),
  (exists (i,t:index), T(i,t) < R1(r) &&
   snd(output@T(i,t)) = snd(input@R1(r)) &&
   fst(output@T(i,t)) = fst(input@R1(r)) &&
   R(r) < T(i,t) &&
   output@R(r) = input@T(i,t)).
by use wa_R1 with r.

fadup 5.

equivalent
  (if
      (exec@pred(R1(r)) &&
       exists (i,t:index),
       ((((T(i,t) < R1(r) && snd(output@T(i,t)) = snd(input@R1(r))) &&
          fst(output@T(i,t)) = fst(input@R1(r)))
         && R(r) < T(i,t))
        && output@R(r) = input@T(i,t)))
    then
      (try find i,t such that
         xor(diff(id(i),id'(i,t)),snd(input@R1(r))) =
         H(<tag0,<nr(r),fst(input@R1(r))>>,diff(key(i),key'(i,t))) in
         xor(diff(id(i),id'(i,t)),
             H(<tag1,<nr(r),fst(input@R1(r))>>,diff(key(i),key'(i,t)))))),
  (if
      (exec@pred(R1(r)) &&
       exists (i,t:index),
       ((((T(i,t) < R1(r) && snd(output@T(i,t)) = snd(input@R1(r))) &&
          fst(output@T(i,t)) = fst(input@R1(r)))
         && R(r) < T(i,t))
        && output@R(r) = input@T(i,t)))
      then
      (try find i,t such that
         exec@pred(R1(r)) &&
	 (T(i,t) < R1(r) &&
          snd(output@T(i,t)) = snd(input@R1(r)) &&
          fst(output@T(i,t)) = fst(input@R1(r)) &&
          R(r) < T(i,t) &&
          output@R(r) = input@T(i,t)) in
         xor(diff(id(i),id'(i,t)),
             H(<tag1,<nr(r),nt(i,t)>>,diff(key(i),key'(i,t)))))).

project.

(* Left *)
fa; try exists i,t.
fa. 
use wa_R1_left with i1,r as [H1 H2]. 
use H1. 
by exists t.
(* Right *)
fa; try exists i,t.
fa. 
use wa_R1_right with i1,t1,r as [H1 H2]. 
by use H1.

fa 5.
fadup 5.
fa 5.
expand seq(i,r,t->xor((diff(id(i),id'(i,t))),
                  H(<tag1,<nr(r),nt(i,t)>>,(diff(key(i),key'(i,t)))))),
       i,r,t.
by fadup 5.

(* Case R2 *)
expand frame@R2(r); expand exec@R2(r).
expand cond@R2(r); expand output@R2(r).
fa 4. fa 5.

(* Same as wa_R1 but with @R2 instead of @R1,
   and the equivalence is used under a negation. *)
equivalent
  (exists (i,t:index), xor(diff(id(i),id'(i,t)),snd(input@R2(r))) =
                 H(<tag0,<nr(r),fst(input@R2(r))>>,diff(key(i),key'(i,t)))),
  (exists (i,t:index), T(i,t) < R2(r) &&
    snd(output@T(i,t)) = snd(input@R2(r)) &&
    fst(output@T(i,t)) = fst(input@R2(r)) &&
    input@T(i,t) = output@R(r) &&   R(r) < T(i,t)).

use tags_neq.
split.
(* proof of lemma: Cond => WA *)
project.
(* left *)
euf Meq.
exists i,t1.
assert (nr(r) = input@T(i,t1)).
fresh Meq1.
by case H0; depends R(r), R1(r).

(* right *)
euf Meq.
exists i,t.
assert (nr(r) = input@T(i,t)).
fresh Meq1.
by case H0; depends R(r), R1(r).

(* proof of lemma: WA => Cond *)
exists i,t.

fadup 5.

(* Case T *)
expand frame@T(i,t). fa 4.
expand seq(i,t->nt(i,t)),i,t.
by expand seq(i,t->xor((diff(id(i),id'(i,t))),
                H(<tag0,<input@T(i,t),nt(i,t)>>,(diff(key(i),key'(i,t)))))),i,t.

(* Case T1 *)
expand frame@T1(i,t); expand exec@T1(i,t).
fa 4. fa 5.

equivalent exec@pred(T1(i,t)) && cond@T1(i,t),
  exec@pred(T1(i,t)) &&
  exists r:index,
  R1(r) < T1(i,t) &&
  input@T1(i,t) = output@R1(r) &&
  T(i,t) < R1(r) &&
  fst(input@R1(r)) = fst(output@T(i,t)) &&
  snd(input@R1(r)) = snd(output@T(i,t)) &&
  R(r) < T(i,t) &&
  input@T(i,t) = output@R(r).
expand cond@T1(i,t); split.
  (* Cond => Honest *)
  assert input@T1(i,t) XOR diff(id(i),id'(i,t)) =
         H(<tag1,<input@T(i,t),nt(i,t)>>,diff(key(i),key'(i,t))).
  use tags_neq; project.
  (* Left *)
  euf Meq0.
  assert R1(r) < T1(i,t) as HClt;
  1: by case H1; depends T(i,t),T1(i,t).
  assert cond@R1(r);
  1: by executable pred(T1(i,t)); use H2 with R1(r); expand exec@R1(r).
  expand cond@R1(r).
  euf Meq2.
  exists r. 
  assert R(r) < T(i,t) as _.
    assert nr(r) = input@T(i,t) as HF.
    fresh HF.
    case H2.  
    case H1.
    by depends R(r),R2(r). 
  (* + *)
  case output@R1(r).
  by euf Meq4.
  by use H2 with i,t.

  (* Right *)
  euf Meq0.
  assert R1(r) < T1(i,t).
    by case H1; depends T(i,t),T1(i,t).
  assert cond@R1(r).
    by executable pred(T1(i,t)); use H2 with R1(r); expand exec@R1(r).
  expand cond@R1(r).
  euf Meq2.
  exists r.
  assert R(r) < T(i,t) as _.
    assert nr(r) = input@T(i,t).
    fresh Meq4.
    by case H2; depends R(r),R2(r).
  case output@R1(r).
  euf Meq4.
  by use H2 with i,t.

  (* Honest => Cond *)
  case output@R1(r).
  project; euf Meq3.
  by use H1 with i,t.

fa 6.
fadup 5.

(* Case T2 *)
expand frame@T2(i,t); expand exec@T2(i,t); expand cond@T2(i,t).
fa 4. fa 5.
equivalent
  (exec@pred(T2(i,t)) &&
   not(input@T2(i,t) =
       diff(id(i),id'(i,t)) XOR H(<tag1,<input@T(i,t),nt(i,t)>>,diff(key(i),key'(i,t))))),
  exec@pred(T2(i,t)) &&
  not(exists r:index,
      R1(r) < T2(i,t) &&
      input@T2(i,t) = output@R1(r) &&
      T(i,t) < R1(r) &&
      fst(input@R1(r)) = fst(output@T(i,t)) &&
      snd(input@R1(r)) = snd(output@T(i,t)) &&
      R(r) < T(i,t) &&
      input@T(i,t) = output@R(r)).
split; use H1.
  (* Honest => Cond *)
  case output@R1(r).
  project; euf Meq3.
  by use H2 with i,t.
  (* Cond => Honest *)
  assert input@T2(i,t) XOR diff(id(i),id'(i,t)) =
         H(<tag1,<input@T(i,t),nt(i,t)>>,diff(key(i),key'(i,t))).
  use tags_neq; project.
  (* Left *)
  euf Meq0.
  assert R1(r) < T2(i,t).
    case H2.
    by depends T(i,t),T2(i,t).
  assert cond@R1(r).
    executable pred(T2(i,t)).
    by use H3 with R1(r); expand exec@R1(r).
  expand cond@R1(r).
  euf Meq2.
  exists r.
  assert R(r) < T(i,t).
    assert nr(r) = input@T(i,t).
    fresh Meq4.
    by case H3; depends R(r),R2(r).
  case output@R1(r).
  euf Meq4.
  use H3 with i,t.

  (* Right *)
  euf Meq0.
  assert R1(r) < T2(i,t).
    by case H2; depends T(i,t),T2(i,t).
  assert cond@R1(r).
    by executable pred(T2(i,t)); use H3 with R1(r); expand exec@R1(r).
  expand cond@R1(r).
  euf Meq2.
  exists r.
  assert R(r) < T(i,t).
    assert nr(r) = input@T(i,t).
    fresh Meq4.
    by case H3; depends R(r),R2(r).
  case output@R1(r).
  euf Meq4.
  by use H3 with i,t.

fa 6.
fadup 5.

Qed.
