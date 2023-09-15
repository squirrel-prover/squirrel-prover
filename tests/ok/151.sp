abstract gt ['a] : 'a -> 'a -> boolean.
abstract ct ['a] : 'a.

lemma [any] _ ['a] (x : 'a) : gt x ct.
