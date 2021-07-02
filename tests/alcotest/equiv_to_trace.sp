system null.

axiom [default/left] check_left : True.
axiom [default/right] check_right : True.

global goal [default/right,default/left] _ (tau:timestamp) :
  equiv(diff(false,true)) ->
  [False].
Proof.
  intro H.
  clear H.
