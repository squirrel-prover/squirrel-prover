(* tests some instantiations of local and global lemmas in global sequents w.r.t.
   adversarial variable tag. *)

name n : message.
name nb : bool.

include Basic.

system null.

(*------------------------------------------------------------------*)
global axiom p ['a] (x : 'a[adv]) : equiv(x).
global axiom q ['a] (x : 'a[adv]) : equiv(x) -> equiv(x).
global axiom s (x : bool[adv]) : [x] -> [x].

axiom r ['a] (x : 'a[adv]) : x = x => x = x.

(* tests the `have` tactic *)
global lemma foo
 ( x, y, z : message     ,  t : timestamp     ) 
 (dx,dy,dz : message[adv], dt : timestamp[adv]) : 
  equiv (x,y,z).
Proof.
  (*     *) have ? := r dx.
  (*     *) have ? := r (dx,dy).
  (*     *) have ? := r true.
  (*     *) have ? := r (fun (a : message) => a = dx).
  checkfail have ? := r x                            exn Failure.
  checkfail have ? := r n                            exn Failure.
  checkfail have ? := r (x,y)                        exn Failure.
  checkfail have ? := r (x,dy)                       exn Failure.
  checkfail have ? := r (fun (a : message) => a = x) exn Failure.

  (*     *) have ? := p dx.
  (*     *) have ? := p (dx,dy).
  (*     *) have ? := p true.
  checkfail have ? := p x      exn Failure.
  checkfail have ? := p n      exn Failure.
  checkfail have ? := p (x,y)  exn Failure.
  checkfail have ? := p (x,dy) exn Failure.

  (*     *) have ? := q dx.
  (*     *) have ? := q (dx,dy).
  (*     *) have ? := q true.
  checkfail have ? := q x      exn Failure.
  checkfail have ? := q n      exn Failure.
  checkfail have ? := q (x,y)  exn Failure.
  checkfail have ? := q (x,dy) exn Failure.

  (*     *) have ? := s true.
  (*     *) have ? := s (dx = dy).
  checkfail have ? := s (x = y) exn Failure.
  checkfail have ? := s nb      exn Failure.
Abort.

(*==================================================================*)
(* check the `apply` tactic *)

global axiom fooM (x,y : message[adv]) : [x = y].

global lemma _ (x : message,y,z: message[adv]) : [x = y] /\ [ y = z].
Proof.
  split. 
  + checkfail apply fooM exn Failure.
    admit.                      (* sub-goal is false *)
  + apply fooM.
Qed.

(*------------------------------------------------------------------*)
(* works on `bool`, as `bool` is a finite fixed-size type *)
global axiom fooB (b : bool[adv]) : [b].

global lemma _ (b1,b2 : bool) : [b1] /\ [b2].
Proof.
  split. 
  + apply fooB.
  + apply fooB.
Qed.
