set smtSteps=10000.

include Core.
include Int.
include Real.
open Int. open Real.

let foo (x : int) = Real.of_int x.

lemma[any] _ (x:Real.t,y:Real.t) : x<y || y<x || x=y. Proof. smt. Qed.

lemma[any] _ (x:Real.t) : x = x. Proof. smt. Qed.
lemma[any] _ (x,y:Real.t) : x+y = y+x. Proof. smt. Qed.
lemma[any] _ (x,y:Real.t) : x*y = y*x. Proof. smt. Qed.

lemma[any] _ (x,y:Real.t) (a,b:int) : of_int 1 * x = x. Proof. smt. Qed.

lemma[any] _ (x,y:Real.t) (a,b:int) : of_int (2*2) * x = of_int 4 * x. 
Proof. smt. Qed.

lemma[any] _ (e:Real.t) (s1,s2:int) : 
   ((of_int ((1 + s1) + s2) * e) 
   - e 
   - of_int s1 * e) 
   - of_int s2 * e 
  = z.
Proof. smt. Qed.

lemma[any] _ (x,y:Real.t) (a,b:int) : x*y = y*x && a*b = b*a. Proof. smt. Qed.

lemma[any] _ (x:Real.t) : x < Real.(+) x (of_int 1). Proof. smt. Qed.

abstract p : int -> bool.

lemma[any] _ : p(1) || (not(p(1))). Proof. smt. Qed.

