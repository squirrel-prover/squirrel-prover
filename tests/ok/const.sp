system null.

global axiom foo (i : index[const]) : [false].

global lemma _ (i : index) : [i = i] -> [false].
Proof. 
  intro H.
  (* `i` is not constant because it appears in `H` *)
  checkfail apply foo i exn Failure. 

  (* clearing `H` yields a constant `i` *)
  clear H. 
  apply foo i.
Qed.

global axiom bar (i : index) : [i = i] -> [false].

abstract a : index.

global lemma _ (i : index) : [i = a] -> [false].
Proof. 
  intro H.
  (* `H` is localized by `const` *)
  const i.
  apply foo i.
Qed.
