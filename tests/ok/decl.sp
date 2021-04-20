set autoIntro=false.

type T
type NL [large]
type NFL [name_fixed_length]
type N [large,name_fixed_length]

abstract f : index -> message.

abstract to_T : message -> T.
abstract from_T : T -> message.

abstract to_N : message -> N.
abstract from_N : N -> message.

abstract N_to_T : N -> T.

abstract ggi ['a] : index -> 'a -> 'a.
abstract gg  ['a] : 'a -> 'a.

name nn : index -> NL.
name nfl : index -> NFL.
name nt : index -> T.

system null.

goal _ (x : message) : gg(zero) = zero.

goal _ (x,y : message) : to_T(x) = to_T(y) => x = y.

goal _ (x : message) : from_T(to_T(x)) = x.

goal _ (x : message) : N_to_T(to_N(x)) = to_T(x).

(* gg is polymorphique *)
goal _ (x : message) : gg(N_to_T(gg(to_N(gg(x))))) = gg(to_T(gg(x))).

(*------------------------------------------------------------------*)
(* check the [large] type info  *)
goal _ (i,j : index) : nn(i) = nn(j) => i = j.
Proof. auto. Qed.

goal _ (i,j : index) : nt(i) = nt(j) => i = j.
Proof. checkfail auto exn GoalNotClosed. Abort.

(*------------------------------------------------------------------*)
(* check the [named_fixed_length] type info  *)
goal _ (i,j : index) : len(nfl(i)) = len(nfl(j)).
Proof.
intro i j. 
by namelength nfl(i), nfl(j).
Qed.

goal _ (i,j : index) : len(nn(i)) = len(nn(j)).
Proof. 
intro i j. 
checkfail (try namelength nn(i), nn(j); auto) exn GoalNotClosed.
Abort.
