set smtSteps=10000.

include Core.
include Int.
open Int.


lemma[any] _ (x:int,y:int) : x<y || y<x || x=y. Proof. smt. Qed.

lemma[any] _ (x:int) : not (exists y:int, y>x && y<x+1). Proof. smt. Qed. 

lemma[any] _ (x:int) : x < x+1. Proof. smt. Qed.

lemma[any] _ (x:int) : exists y:int, x = y+1. Proof. smt. Qed. 

abstract p : int -> bool.

lemma[any] _ : p(1) || (not(p(1))). Proof. smt. Qed.

