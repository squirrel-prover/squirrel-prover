(* small tests on search and tuples *)

name n : index * index -> message.
abstract namelength_1 : message.

axiom [any] namelength_n2 :
  forall (i,j:index), len (n(i,j)) = namelength_1.

(* search len. *)
search len _.

search n(_).

axiom [any] namelength_n1 :
  forall (i:index * index), len (n(i)) = namelength_1.

search n _.
search n(_,_).
