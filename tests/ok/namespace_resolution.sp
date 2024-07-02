include Basic.

system null.

namespace A.
  namespace B.
    op a = empty.
  end B.
end A.

namespace C.
  axiom _ : A.B.a = empty.
  open A.
  (* B resolves to [A.B] because [A] was brought in scope *)
  open B. 
  axiom _ : a = empty.
end C.

(*------------------------------------------------------------------*)
op foo = zero.

namespace Foo.
  op foo = empty.
end Foo.

lemma [any] _ : Foo.foo = empty.
Proof.
 rewrite /Foo.foo.
 apply eq_refl.  
Qed.

lemma [any] _ : Foo.foo = empty.
Proof.
 rewrite /foo.
 apply eq_refl.  
Qed.

lemma [any] _ : foo = zero.
Proof.
 checkfail rewrite /Foo.foo exn Failure.
 rewrite /foo.
 apply eq_refl.  
Qed.
