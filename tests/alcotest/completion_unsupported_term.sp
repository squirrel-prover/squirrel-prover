abstract ok : message
abstract ko : message

system null.

goal _ :(try find i such that i=i in ok) = (try find i such that i=i in ko).
Proof.
simpl.
Qed.
