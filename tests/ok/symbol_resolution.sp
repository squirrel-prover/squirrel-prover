include Core.

type T.
type A.
type B.
type C.

op t : T -> message = fun _ => empty.
op a : A -> message = fun _ => witness.
op b : B -> message = fun _ => witness.
op c : C -> message = fun _ => witness.

op x = t.
op (+) : T -> T -> bool.

namespace A.
  op foo : message.

  op x = a.

  op (+) : A -> A -> bool.
  namespace B.
    op (+) : B -> B -> bool.
    op x = b.
  end B.
end A.

namespace C.
  op (+) : C -> C -> bool.
  op x = c.
end C.

(* same type signatures as in `C` *)
namespace C2.
  op (+) : C -> C -> bool.
  op x = c.
end C2.

lemma [any] _ : x = t.
Proof.
 rewrite /x.
 apply eq_refl.  
Qed.

lemma [any] _ : A.x = a.
Proof.
 rewrite /x.
 apply eq_refl.  
Qed.

lemma [any] _ : A.B.x = b.
Proof.
 rewrite /x.
 apply eq_refl.  
Qed.

lemma [any] _ : C.x = c.
Proof.
 rewrite /x.
 apply eq_refl.  
Qed.

lemma [any] _ : C2.x = c.
Proof.
 rewrite /x.
 apply eq_refl.  
Qed.

(*------------------------------------------------------------------*)
open A.
open B.
open C.

lemma [any] _ (xt : T) (xa : A) (xb : B) (xc : C) : false. 
Proof.
 nosimpl have ? : x xt = empty by auto.

 nosimpl have ? : x xa = A.x xa by auto.

 nosimpl have ? : x   xb = A.B.x xb by auto.
 nosimpl have ? : B.x xb = A.B.x xb by auto.

 nosimpl have ? : x xc = C.x xc by auto.

 nosimpl have ? : xt + xt = witness by admit.

 nosimpl have ? : xa + xa = A.(+) xa xa by auto. 

 nosimpl have ? : xb + xb = B.(+) xb xb by auto.

 nosimpl have ? : xc + xc = C.(+) xc xc by auto.
Abort.

(*------------------------------------------------------------------*)
(* open `C2`, now there is an ambiguity between `C.x` and `C2.x` 
  (idem `C.(+)` and `C2.(+)`) *) 
open C2.

lemma [any] _ (xc : C) : false. 
Proof.
 (* nosimpl have ? : x xc = C.x xc by auto. *)
 (* Conversion Error: could not desambiguate *)

 (* nosimpl have ? : xc + xc = C.(+) xc xc by auto. *)
 (* Conversion Error: could not desambiguate *)

 nosimpl have ? : C.x xc = C2.x xc by auto.
 nosimpl have ? : C.x xc = C2.x xc by auto.
Abort.

(*------------------------------------------------------------------*)
close A.
close A.B.
close C.
