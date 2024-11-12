system null.

abstract b   : bool.
abstract b'  : bool.
abstract b'' : bool.

global axiom foo : 
  Let t = true in 
  [b] -> [b'].

global lemma _:
  [b] -> [false].
Proof.
  intro Hb.
  have H:= foo.
  have H0 := H Hb. 
Abort.
