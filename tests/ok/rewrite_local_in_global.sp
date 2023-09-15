system null.

global lemma _ ['a] (x,y,z : 'a) : [x = y] -> [x = z => false].
Proof. 
  intro H. 
  intro G. 
  (* We are not allowed to rewrite a local hypothesis in a global 
     hypothesis! *)
  checkfail rewrite G in H exn NothingToRewrite.
Abort.
