type T[finite].

system null.

name m : message.

name n  : T -> message.
name n0 : index -> message.

axiom _ i : n  i <> m. 
axiom _ i : n0 i <> m. 

global axiom _ i : [n  i <> m]. 
global axiom _ i : [n0 i <> m]. 
