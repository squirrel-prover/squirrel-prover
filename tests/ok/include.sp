

include TestInclude.

abstract ToMessage : T -> message.

goal tm_apply (x,y: T) : x = y => ToMessage(x) = ToMessage(y).
Proof. auto. Qed.

goal _ (x,y : T) : x = y => f (ToMessage(x)) = f (ToMessage(y)).
Proof. 
  intro H.
  apply tm_apply in H.
  apply f_apply in H.
  assumption.
Qed.
