include Logic.
include Int.
open Int.

(*------------------------------------------------------------------*)
inductive list a = 
| Nil : list a
| Cons : a -> list a -> list a.

lemma cons_inj @system:any ['a] (x, y:'a) (l1, l2:list 'a) :
  Cons x l1 = Cons y l2 =>  x = y && l1 = l2.
Proof. smt. Qed.

lemma nil_not_cons @system:any ['a] (x:'a) (l:list 'a) : 
 not (Nil = Cons x l).
Proof. smt. Qed.

lemma nil_or_cons @system:any ['a] (l:list 'a) :
  l = Nil || (exists (x:'a) (l2:list 'a), l = Cons x l2).
Proof. smt. Qed.

lemma loop @system:any ['a]:
 exists (x:'a) (l:list 'a), l = Cons x l.
Proof.
  checkfail smt exn Failure. 
Abort.

(*------------------------------------------------------------------*)
let rec append_rev ['a] (l1 : list 'a) (l2 : list 'a) : list 'a with
| Nil -> l1
| Cons a l2 -> append_rev (Cons a l1) l2.
Proof. 
  intro > <-; discriminate. 
Qed.

(*------------------------------------------------------------------*)
(* reverse [l1] and concatenate it with [l2] *)
let rev_append ['a] (l1 : list 'a) (l2 : list 'a) : list 'a =
  append_rev l2 l1.

(*------------------------------------------------------------------*)
let rev ['a] (l : list 'a) : list 'a = append_rev Nil l.

(*------------------------------------------------------------------*)
let append ['a] (l1 : list 'a) (l2 : list 'a) : list 'a =
  append_rev l1 (rev l2).

(*------------------------------------------------------------------*)
let rec length ['a] (x : list 'a) : int with
| Nil -> 0
| Cons _ l -> 1 + length l.
Proof.
  intro > <-; discriminate. 
Qed.

(*------------------------------------------------------------------*)
lemma length_nil @system:any ['a] :
  length Nil['a] = 0.
Proof. smt. Qed. 

lemma length_neg @system:any ['a] : 
  exists (l:list 'a), length l < 0.
Proof. 
  checkfail smt exn Failure.
Abort.

exact lemma length_append_rev @system:any ['a] (l1,l2 : list 'a) :
  length (append_rev l1 l2) = length l1 + length l2.
Proof. 
  generalize l1.
  induction l2; smt.
Qed.

hint smt length_append_rev.

lemma length_rev @system:any ['a] (l : list 'a) :
  length (rev l) = length l.
Proof. smt. Qed.

lemma rev_sanity @system:any ['a] (l: list 'a) :
  rev l = l.
Proof.
  checkfail smt exn Failure.
Abort.
