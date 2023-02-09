type T1[finite].
type T2.

name n0 : index -> message.
name n1 : index -> index.
name n2 : index -> bool.
name n3 : index -> T2.

name m0 : T1 -> message.
name m1 : T1 -> index.
name m2 : T1 -> bool.
name m3 : T1 -> T2.

name l0 : (T1 * index * bool) -> message.
name l1 : (T1 * index * bool) -> index.
name l2 : (T1 * index * bool) -> bool.
name l3 : (T1 * index * bool) -> T2.

name p0 : (index -> bool) -> message.
name p1 : (index -> bool) -> index.
name p2 : (index -> bool) -> bool.
name p3 : (index -> bool) -> T2.

name q0 : (T1 -> bool) -> message.
name q1 : (T1 -> bool) -> index.
name q2 : (T1 -> bool) -> bool.
name q3 : (T1 -> bool) -> T2.
