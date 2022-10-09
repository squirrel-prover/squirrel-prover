channel c.

type T
type L  [large]

abstract f : index -> message.

abstract to_T : message -> T.
abstract from_T : T -> message.

abstract to_L : message -> L.
abstract from_L : L -> message.

abstract L_to_T : L -> T.

abstract ggi ['a] : index -> 'a -> 'a.
abstract gg  ['a] : 'a -> 'a.

mutable lstate : L = to_L(empty).

(*------------------------------------------------------------------*)
process B (i : index) =
 in(c,x);
 new m : message;
 new l : L;
 new t : T;
 let a = <x,<m,from_L(l)>> in
 let y = gg(to_L(a)) in
 let z = ggi i (L_to_T(y)) in
 out (c, from_T(z)).

system !_i B(i).

(*------------------------------------------------------------------*)
(* same with explicit types *)
process B2 (i : index) =
 in(c,x);
 new m : message;
 new l : L;
 new t : T;
 let a = <x,<m,from_L(l)>> in
 let y : L = gg(to_L(a)) in
 let z : T = ggi i (L_to_T(y)) in
 out (c, from_T(z)).

system [Two] !_i B2(i).

(*------------------------------------------------------------------*)
process B3 (i : index) =
 in(c,x);
 new l : L;
 let gl : L = ggi i l in
 out (c, from_L(gl)).

system [Three] !_i B3(i).

(*------------------------------------------------------------------*)
process State (i : index) =
 in(c,x);
 new l : L;
 lstate := ggi i l;
 out (c, empty).

system [StateTest] !_i State(i).
