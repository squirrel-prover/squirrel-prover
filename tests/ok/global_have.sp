(* tests some instantiations of local and global lemmas in global sequents. *)

include Basic.

system null.

(*------------------------------------------------------------------*)
global lemma bar ['a 'b 'c] (b : bool, d: 'b, x : 'a, y : 'b, z : 'c) : 
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

global lemma foo (x,y,z : message, t : timestamp) : equiv (x,y,z).
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

global lemma _ (b1,b2: bool) : [b1].
Proof.
  (* succeed, [b] instantiated by [b1] *)
  nosimpl(have A := foo b1).
  assumption A.
Qed.

global lemma _ (b1,b2: bool) : [b1].
Proof.
  (* idem with an apply, check that matching verifies tags *)
  apply foo.
Qed.

global lemma _ (b1,b2: bool) : [diff(b1,b2)].
Proof.
  (* should fail since we cannot instantiate [b] in [foo] by a diff. *)
  checkfail have A := foo (diff(b1,b2)) exn Failure.
Abort.

global lemma _ (b1,b2: bool) : [diff(b1,b2)].
Proof.
  (* idem with an apply *)
  checkfail apply foo exn Failure.
Abort.

(*------------------------------------------------------------------*)
lemma _ : false.
Proof. 
  have ? := ax_bool true. 

  (* `q` as equivalences, but the current system context does not have
      a `equiv` field. Thus, it is not possible to add `q` as an hypothesis. *)
  checkfail have ? := q empty exn NoAssumpSystem.
  checkfail have ? := q empty _; 1: auto exn NoAssumpSystem. Abort.

(*------------------------------------------------------------------*)
(* we can add `q` by manually setting the `equiv` field of the sequent to 
   the appropriate value *)
lemma [set:default; equiv:default] _ : false.
Proof. 
  have ? := ax_bool true. 
  have ? := q empty.
  have ? := q empty _; 1: auto.
Abort.
