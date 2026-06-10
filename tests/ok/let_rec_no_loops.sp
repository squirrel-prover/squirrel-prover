include Core.
include "Data/List.sp".
include Int.
open Int.


let rec zeros ~admit_ptime (n:int) = if n=0 then Nil else Cons 0 (zeros (n-1)).
Proof.
smt.
Qed.

global lemma [any] ded_zero : $( () |> (zeros 0)).
Proof.
deduce.
rewrite /zeros.
deduce.
rewrite if_true //.
by deduce.
Qed.

global lemma [any] ded : Forall (n:_[const]), $( () |> (zeros n)).
Proof.
induction.
intro n IH.
ghave [C | C] : [n=0 || n <>0] by auto.
 - rewrite C. deduce with ded_zero.
 - expand (zeros n). 
   rewrite (if_false (n=0)) // /=.

   deduce with (IH (n-1)).
   smt. 
Qed.
