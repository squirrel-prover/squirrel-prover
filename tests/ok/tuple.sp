type int.

abstract foo : int * int -> int.

abstract foo0 : int * int.

op bar (x : int * int) : int * int = x.

mutable s : int * int = foo0.

goal [any] _ (x : int * int) : x = x.
Proof. auto. Qed.

goal [any] _ (x : int * (int * int)) : x = x.
Proof. auto. Qed.

goal [any] _ (x : (int * int) * int) : x = x.
Proof. auto. Qed.
