(* various parser checks *)

system null.

(* --------------------------------------------------------- *)
predicate Foo0 ['a] {S1} (x : 'a) y z = [x = y && y = z].

predicate Foo1 {S1       S2[pair]}.
predicate Foo2 {S2[pair] S1      }.

predicate Foo3 ['a] { } (x : 'a) y z = [x = y && y = z].

predicate Foo4 ['a] {S1 S2} {S1 : (x : 'a)} {S2 : y,z : 'a} (u : 'a) v w =
  [u = v && v = w].

predicate Foo5 ['a] {set equiv S}
  {set: (x : bool)} {equiv: y,z : 'a} {S: a : 'a} (u : 'a) v w 
 =
 [u = v && v = w] /\ equiv(y,z,u,v,w) /\ [x => v = w].

global axiom _ : $(Foo0{[default]} empty empty empty).

global axiom _ : $(Foo1{[default] [default]}).

global axiom _ : $(Foo2{[default/left, default/right] [default]}).

predicate a0 ['a 'b] {set} {set: (u : 'a, v : 'b)} =
  Exists (f : ('a -> 'b)[adv]), [f u = v].

predicate a1 ['a 'b] {set equiv} {set: (u : 'a, v : 'b)} {equiv: (x : 'b)} =
  Exists (f : ('a -> 'b)[adv]), [f u = v] /\ equiv(x).

predicate a2 ['a 'b] {set equiv} {set: (u : 'a, m : 'b)} {equiv: x : message} =
  Exists (f : ('a -> 'b)[adv]), [f u = m] /\ equiv(x).
