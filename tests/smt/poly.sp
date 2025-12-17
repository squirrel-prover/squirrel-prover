set smtSteps=10000.

abstract c['b] : 'b.
abstract g['a] : 'a -> bool.
abstract h['a 'b] : 'a -> 'b.

lemma[any] _ (x:bool) : g(x) || not(g(x)). Proof. smt. Qed.

lemma[any]_ (x:bool,y:message) : g(x) || not(g(x)) && g(y) || not(g(y)). Proof. smt. Qed.

lemma[any] _ ['a 'b] : g['a](c) || (not (g['a](c))). Proof. smt. Qed.

lemma[any] _['a] : (exists x:'a, g(x)) || not (exists x:'a, g(x)).
Proof. checkfail (smt ~no_poly) exn Failure. smt. Qed.

lemma[any] _ ['a 'b] : g['a](c) || (not (g['a](c))). Proof. smt. Qed.

lemma[any] _ ['a 'b] (f:'a->bool) : f(c) || (not (f(c))). Proof. smt. Qed.

lemma[any] _ ['b] (x:'b) : h x || not (h x).  Proof. smt. Qed.

lemma[any] _ : c || not c. Proof. smt. Qed.

abstract p['a] : bool.

lemma[any] _ : p[int] || not p[bool]. Proof. checkfail smt exn Failure. Abort.
