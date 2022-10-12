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

axiom r ['a] (x : 'a) : x = x => x = x.

global goal foo (x,y,z : message) : equiv (x,y,z).
Proof.
  have ? := r x.
  have ? := p x.
  have ? := q x.
  have ? := bar true empty x y z.
  apply bar true empty.
Abort.
