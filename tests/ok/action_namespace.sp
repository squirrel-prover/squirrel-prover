channel c.

namespace T.
  process B = out(c,witness).
  system SB = B.

  lemma [SB] _ : false. 
  Proof.
    have ? : B = init.
    have ? : T.B = init.
  Abort.
end T.

lemma [T.SB] _ : false. 
Proof.
  have ? : T.B = init.
Abort.
