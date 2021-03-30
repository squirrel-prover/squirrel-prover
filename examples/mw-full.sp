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

set autoIntro=false.
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
goal tags_neq0 : tag0 = tag1 => False. 
Proof. 
 use tags_neq; auto. 
Qed.

(* Well-authentication for R1's condition, formulated in an imprecise
   way with respect to the involved indices. *)
goal wa_R1 (r:index) :
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

  intro r; split.

  (* Cond => WA *)
  intro [i t Meq].
  project. 
  (* left *)
  euf Meq => _ _ _; 1: auto.
  exists i,t0; simpl.
  assert (input@T(i,t0) = nr(r)) as F; 1: auto.
  fresh F => C.
  by case C; 1: depends R(r), R2(r).
  (* right *)
  euf Meq => _ _ _; 1:auto.
  exists i,t; simpl.
  assert (input@T(i,t) = nr(r)) as F; 1: auto.
  fresh F => C.
  by case C; 1: depends R(r), R2(r).

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
  snd(output@T(i,t)) = snd(input@R1(r)) &&
  fst(output@T(i,t)) = fst(input@R1(r)) &&
  R(r) < T(i,t) &&
  output@R(r) = input@T(i,t).
Proof.
  intro i r.
  split; 2: by intro [_ _]; expand output.
  intro Meq; euf Meq => _ _ _; 1: auto.
  exists t; simpl.
  assert input@T(i,t) = nr(r) as F; 1: auto.
  fresh F => C.
  by case C; 1:depends R(r), R2(r).
Qed.

(** Precise version of wa_R1 on the right: no more existentials. *)
goal [right] wa_R1_right (i,t,r:index):
  xor(id'(i,t),snd(input@R1(r))) =
  H(<tag0,<nr(r),fst(input@R1(r))>>,key'(i,t))
  <=>
  T(i,t) < R1(r) &&
  snd(output@T(i,t)) = snd(input@R1(r)) &&
  fst(output@T(i,t)) = fst(input@R1(r)) &&
  R(r) < T(i,t) &&
  output@R(r) = input@T(i,t).
Proof.
  intro i t r.
  split; 2: by intro [_ _]; expand output.
  intro Meq; euf Meq => _ _ _; 1: auto.
  assert input@T(i,t) = nr(r) as F; 1: auto.
  fresh F => C.
  by case C; 1:depends R(r), R2(r).  
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

enrich seq(r -> nr(r)),
       seq(i,t -> nt(i,t)),
       seq(i,t -> diff(id(i),id'(i,t)) XOR
                  H(<tag0,<input@T(i,t),nt(i,t)>>,diff(key(i),key'(i,t)))),
       seq(i,r,t -> diff(id(i),id'(i,t)) XOR
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
fa; [1,2: by intro [_ [i t _]]; simpl; exists i,t |
     4: auto].
intro [_ [i t _]].
fa; 2,3,4: intro *; expand output; auto.
intro Meq.
use wa_R1_left with i0,r as [H1 H2]. 
use H1 as [_ _]; 2: expand output; auto.
by expand output; exists t. 
(* Right *)
fa; [1,2: by intro [_ [i t _]]; simpl; exists i,t |
     4: auto].
intro [_ [i t _]].
fa; 2,3,4: intro *; expand output; auto.
intro Meq; simpl.
use wa_R1_right with i0,t0,r as [H1 H2].
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
intro [i t Meq].
project.
(* left *)
euf Meq => _ _ _; 1:auto.
exists i,t0; simpl.
assert (nr(r) = input@T(i,t0)) as F; 1:auto.
fresh F => C.
by case C; 2:depends R(r), R1(r).

(* right *)
euf Meq => _ _ _; 1:auto.
exists i,t; simpl.
assert (nr(r) = input@T(i,t)) as F; 1:auto.
fresh F => C.
by case C; 2:depends R(r), R1(r).

(* proof of lemma: WA => Cond *)
by intro [i t _]; expand output; exists i,t.

by fadup 5.

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
  intro [_ Meq]; simpl.
  assert input@T1(i,t) XOR diff(id(i),id'(i,t)) =
         H(<tag1,<input@T(i,t),nt(i,t)>>,diff(key(i),key'(i,t)));
  1: auto.
  use tags_neq; project.
  (* Left *)
  simpl.
  euf Meq0 => Ctrace [_ [A B]] _; 2:auto.
  assert R1(r) < T1(i,t) as HClt;
  1: by case Ctrace; depends T(i,t),T1(i,t).
  clear Ctrace.
  assert cond@R1(r) as Hcond.
    executable pred(T1(i,t)); 1,2: auto.
    by intro HH; use HH with R1(r); expand exec@R1(r).
  expand cond@R1(r).
  destruct Hcond as [i1 t1 Hcond].
  euf Hcond => _ [_ [_ _]] _; 1:auto.
  exists r; simpl.
  assert R(r) < T(i,t) as _.
    assert nr(r) = input@T(i,t) as HF; 1:auto.
    fresh HF => C.
    case C; 2,3:auto. 
    by depends R(r),R2(r). 
  simpl.
  case output@R1(r).
  by euf Meq1.
  by use H0 with i,t.

  (* Right *)
  euf Meq0 => Ctrace [_ [A B]] [? ?]; 2: auto.
  simpl.
  assert R1(r) < T1(i,t) as Clt.
    by case Ctrace; depends T(i,t),T1(i,t).
  clear Ctrace.
  assert cond@R1(r) as Hcond.
    executable pred(T1(i,t)); 1,2: auto.
    by intro Hex; use Hex with R1(r); expand exec@R1(r).
  expand cond@R1(r).
  destruct Hcond as [i1 t1 Hcond].
  euf Hcond => Clt1 [_ [D F]] [? ?]; [1:auto].
  exists r; simpl.
  assert R(r) < T(i,t) as _.
    assert nr(r) = input@T(i,t) as HF; 1:auto.
    fresh HF => C.
    by case C; [1: depends R(r),R2(r) |
                2: depends R(r),R1(r)].
  simpl.
  case output@R1(r).
  euf Meq1 => A0 [A1 _] [_ _]; 1,2: by auto.
  by use H0 with i,t. 

  (* Honest => Cond *)
  intro [_ [r _]]; simpl.
  case output@R1(r); expand output.
  by project; euf Meq.

  by use H0 with i,t.

fa 6.
by fadup 5.

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
split; intro [_ H1]; simpl.
  (* Honest => Cond *)
  intro [r H2]; use H1.
  case output@R1(r); expand output.
  (* by project; euf Meq. *)
  by project; euf Meq => _ [F _] *.
  by use H0 with i,t.
  (* Cond => Honest *)
  intro Meq.
  use H1.
  assert input@T2(i,t) XOR diff(id(i),id'(i,t)) =
         H(<tag1,<input@T(i,t),nt(i,t)>>,diff(key(i),key'(i,t))); 1:auto.
  use tags_neq; project.
  (* Left *)
  euf Meq0 => Ct _ _; 2:auto.
  assert R1(r) < T2(i,t) as _.
    by case Ct; try depends T(i,t),T2(i,t).
  clear Ct.
  assert cond@R1(r) as Hcond.
    executable pred(T2(i,t)); 1,2: auto.    
    by intro He; use He with R1(r); expand exec@R1(r).
  expand cond@R1(r).
  destruct Hcond as [i1 t1 Hcond]. 
  euf Hcond => _ _ _; 1: auto.
  exists r; simpl.
  assert R(r) < T(i,t).
    assert nr(r) = input@T(i,t) as HF; 1: auto.
    fresh HF => C.
    by case C; 1: depends R(r),R2(r). 
  simpl.
  case output@R1(r).
  by euf Meq1.
  by use H0 with i,t.

  (* Right *)
  euf Meq0 => Ct _ [_ _]; 2:auto.
  assert R1(r) < T2(i,t) as _.
    by case Ct; depends T(i,t),T2(i,t).
  clear Ct.
  assert cond@R1(r) as Hcond.
    executable pred(T2(i,t)); 1,2: auto => He.
    by use He with R1(r); expand exec@R1(r). 
  expand cond@R1(r).
  destruct Hcond as [i1 t1 Hcond].
  euf Hcond; 1: auto => _ _ [_ _].
  exists r; simpl.
  assert R(r) < T(i,t) as _.
    assert nr(r) = input@T(i,t) as HF; 1: auto.
    fresh HF => C.
    by case C; 1: depends R(r),R2(r).
  simpl.
  case output@R1(r).
  by euf Meq1.
  by use H0 with i,t.

fa 6. 
by fadup 5.

Qed.
