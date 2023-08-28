include Basic.

type int.

abstract i0 : int.
abstract i1 : int.

axiom [any] _ : (fun (_ : int) => i0) = (fun (_ : int) => i1).
axiom [any] _ : (fun (_ : int) => i0) = (fun (_ :   _) => i1).

axiom [any] _ (x : int) : (fun (_:   _) => i0) x = i1.
axiom [any] _ (x :   _) : (fun (_: int) => i0) x = i1.

axiom [any] _ ['a] (x : 'a) y : x = y.
axiom [any] _ ['a] x (y : 'a) : x = y.
