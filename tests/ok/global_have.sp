(* tests some instantiations of local and global lemmas in global sequents. *)

include Basic.

system null.

(*------------------------------------------------------------------*)
global goal bar ['a 'b 'c] (b : bool, d: 'b, x : 'a, y : 'b, z : 'c) : 
  equiv (x, b, if b then y else d, if not b then y else d, z) ->
  equiv (x, y, z).
Proof.
  intro H.
  have ->: y = if b then (if b then y else d) else (if not b then y else d) 
  by case b.
  apply H.
Qed.

global axiom p ['a] (x : 'a) : (* equiv(x) ->  *)equiv(x).
global axiom q ['a] (x : 'a) : equiv(x) -> equiv(x).

global axiom ax_bool (x : bool) : [x] -> [x].

axiom r ['a] (x : 'a) : x = x => x = x.

axiom ax_bool_loc (x : bool[const]) : x.

global goal foo (x,y,z : message, t : timestamp) : equiv (x,y,z).
Proof.
  have ? := r x.
  have ? := p x.
  have ? := q x.
  have ? := bar true empty x y z.

  have ? := r true.
  have ? := p true.
  have ? := q true.

  (* check that instantiation of global cannot be done on terms which
     are not system-independent *)
  checkfail have ? := q (frame@t) exn Failure.
  checkfail have ? := q (diff(x,y)) exn Failure.

  (* same with `ax_bool` *)
  checkfail have ? := ax_bool (cond@t) exn Failure.
  checkfail have ? := ax_bool (diff(true,true)) exn Failure.

  (* same with `ax_bool` *)  
  checkfail have ? := ax_bool_loc (cond@t) exn Failure. 

  apply bar true empty.
Abort.

(*------------------------------------------------------------------*)
global axiom foo (b : bool) : [b].

global goal _ (b1,b2: bool) : [b1].
Proof.
  (* succeed, [b] instantiated by [b1] *)
  nosimpl(have A := foo b1).
  assumption A.
Qed.

global goal _ (b1,b2: bool) : [b1].
Proof.
  (* idem with an apply, check that matching verifies tags *)
  apply foo.
Qed.

global goal _ (b1,b2: bool) : [diff(b1,b2)].
Proof.
  (* should fail since we cannot instantiate [b] in [foo] by a diff. *)
  checkfail have A := foo (diff(b1,b2)) exn Failure.
Abort.

global goal _ (b1,b2: bool) : [diff(b1,b2)].
Proof.
  (* idem with an apply *)
  checkfail apply foo exn Failure.
Abort.
