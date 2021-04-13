type T
type N [large,bounded]

abstract f : index -> message.

abstract to_T : message -> T.
abstract from_T : T -> message.

abstract to_N : message -> N.
abstract from_N : N -> message.

abstract N_to_T : N -> T.

abstract ggi ['a] : index -> 'a -> 'a.
abstract gg  ['a] : 'a -> 'a.

system null.

goal _ (x : message) : gg(zero) = zero.

goal _ (x,y : message) : to_T(x) = to_T(y) => x = y.

goal _ (x : message) : from_T(to_T(x)) = x.

goal _ (x : message) : N_to_T(to_N(x)) = to_T(x).

(* gg is polymorphique *)
goal _ (x : message) : gg(N_to_T(gg(to_N(gg(x))))) = gg(to_T(gg(x))).

