op nand (x : bool, y : bool) : bool = not(x && y).

lemma[any] _ (x,y:bool) : nand x y = ((not x) || (not y)). Proof. smt. Qed.
