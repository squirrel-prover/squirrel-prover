system null.

global axiom foo (i : index) : ([i = i]) -> [false].
axiom bar (i : index) : (i = i) => false.

global lemma _ (i,j : index[const]) : [i = i] -> [i = j].
Proof.
  intro A. 
  have ? := foo.
  use foo.
Abort.
