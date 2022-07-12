

system null.

goal _ (x, y : message) : x = <y,y> => <x,x> = <<y,y>,<y,y>>.
Proof.
 intro H.
 remember <x,x> as z => G.
Abort.
