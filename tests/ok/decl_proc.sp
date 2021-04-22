set autoIntro=false.

channel c.

type T
type L [large]

abstract f : index -> message.

abstract to_T : message -> T.
abstract from_T : T -> message.

abstract to_L : message -> L.
abstract from_L : L -> message.

abstract L_to_T : L -> T.

abstract ggi ['a] : index -> 'a -> 'a.
abstract gg  ['a] : 'a -> 'a.

process B (i : index) =
 in(c,x);
 new m : message;
 new l : L;
 new t : T;
 let a = <x,<m,l>> in
 let y = gg(to_L(a)) in
 let z = ggi(i,L_to_T(y)) in
 out (c, from_T(z)).

(* same with explicit types *)
process B2 (i : index) =
 in(c,x);
 new m : message;
 new l : L;
 new t : T;
 let a = <x,<m,l>> in
 let y : L = gg(to_L(a)) in
 let z : T = ggi(i,L_to_T(y)) in
 out (c, from_T(z)).

system       !_i B(i).
system [Bis] !_i B2(i).
