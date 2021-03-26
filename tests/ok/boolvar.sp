set autoIntro=false.

system null.

goal _ (b : boolean, x,y : message) :
 x XOR y = x.

goal _ (b : boolean, x,y : message) :
if b then x else y = y.

goal _ (b : boolean, x,y : message) :
 (not b) => if b then x else y = y.
