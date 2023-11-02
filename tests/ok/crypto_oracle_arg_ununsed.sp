include Basic.

system [E] null.

abstract a : message
abstract b : message

game Bar = {
  oracle g (x : message) = { 
    return diff(a,b)
  }
}.

(* Not_found dans crypto.ml, line 1076, car `x` n'a pas été trouvé par 
   le matching *)
global lemma [E] _ :
  equiv(diff(a,b)).
Proof.
  crypto Bar.
Qed.
