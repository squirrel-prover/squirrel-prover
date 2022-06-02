

system null.

type T [large].

name nT : T.

abstract gT : T -> message.

abstract f : message -> message.

abstract cst : message.

goal f_apply (x,y:message) : x = y => f(x) = f(y).
Proof. auto. Qed.

