

system null.

axiom _ (b : boolean, x,y : message) :
 x XOR y = x.

axiom _ (b : boolean, x,y : message) :
if b then x else y = y.

axiom _ (b : boolean, x,y : message) :
 (not b) => if b then x else y = y.
