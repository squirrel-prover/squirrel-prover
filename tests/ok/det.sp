(* tests some instantiations of local and global lemmas in global sequents w.r.t.
   determinism. *)

name n : message.
name nb : bool.
include Basic.

system null.

(*------------------------------------------------------------------*)
global axiom p ['a] (x : 'a[const]) : (* equiv(x) ->  *)equiv(x).
global axiom q ['a] (x : 'a[const]) : equiv(x) -> equiv(x).
global axiom s (x : bool[const]) : [x] -> [x].

axiom r ['a] (x : 'a[const]) : x = x => x = x.

(* tests the `have` tactic *)
global goal foo
 ( x, y, z : message     ,  t : timestamp     ) 
 (dx,dy,dz : message[const], dt : timestamp[const]) : 
equiv (x,y,z).
Proof.
  (*     *) have ? := r dx.
  (*     *) have ? := r (dx,dy).
  (*     *) have ? := r true.
  checkfail have ? := r x      exn Failure.
  checkfail have ? := r n      exn Failure.
  checkfail have ? := r (x,y)  exn Failure.
  checkfail have ? := r (x,dy) exn Failure.

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

global axiom fooM (x,y : message[const]) : [x = y].

global goal _ (x : message,y,z: message[const]) : [x = y] /\ [ y = z].
Proof.
  split. 
  + checkfail apply fooM exn Failure.
    admit.                      (* sub-goal is false *)
  + apply fooM.
Qed.

(*------------------------------------------------------------------*)
(* works on `bool`, as `bool` is a finite fixed-size type *)
global axiom fooB (b : bool[const]) : [b].

global goal _ (b1,b2 : bool) : [b1] /\ [b2].
Proof.
  split. 
  + apply fooB.
  + apply fooB.
Qed.
