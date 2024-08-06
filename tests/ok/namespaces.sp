include Core.

namespace Foo.
  op ( * )  x y = <x,y>.
  op ( - )  x y = <x,y>.
  op ( + )  x y = <x,y>.
  op ( ++ )   x y = <x,y>.
  op ( ++1+ ) x y = <x,y>.

  lemma [any] _ x y : x ++1+ y = x ++ y && x ++ y = x * y.
  Proof. 
    rewrite /Foo.( * ). 
    (* rewrite /(++). *)
  Abort.

  op f : message = empty.
  type t.
  abstract a : t.

  namespace Bar.
    type t.
    op f : message = zero.
  end Bar.
end Foo.

(* --------------------------------------------------------- *)
op foo : Foo.t -> Foo.Bar.t -> Foo.t * Foo.Bar.t = fun x y => (x,y).

op bar0 : Foo.t = Foo.a.

(* --------------------------------------------------------- *)
lemma [any] _ : Foo.f = empty.
Proof.
  rewrite /Foo.f.
  apply eq_refl.
Qed.

lemma [any] _ : Foo.Bar.f = zero.
Proof.
  rewrite /Foo.Bar.f.
  apply eq_refl.
Qed.

lemma [any] _ : Foo.f = Foo.Bar.f.
Proof.
  checkfail auto exn GoalNotClosed.
  rewrite /Foo.f /Foo.Bar.f.
  checkfail auto exn GoalNotClosed.
Abort.

(* --------------------------------------------------------- *)
(* open Foo again *)
namespace Foo.
  op g : message = Foo.Bar.f.
end Foo.

lemma [any] _ : Foo.g = Foo.Bar.f. Proof. auto. Qed.

(* --------------------------------------------------------- *)
(* open *)

namespace T1.
  open Foo.

  lemma [any] _ : f = Foo.f.     Proof. auto. Qed.
  lemma [any] _ : f = Foo.Bar.f. Proof. checkfail auto exn GoalNotClosed. Abort.
end T1. 

namespace T2.
  open Foo.Bar.

  lemma [any] a : f = Foo.f.     Proof. checkfail auto exn GoalNotClosed. Abort.
  lemma [any] a : f = Foo.Bar.f. Proof. auto. Qed.
end T2.

namespace T3.
  open Foo.
  op bar   :     t =     a.
  op bar'  : Foo.t =     a.
  op bar'' :     t = Foo.a.

  lemma [any] _ : bar = bar' && bar' = bar''. Proof. auto. Qed.
end T3.

(* --------------------------------------------------------- *)
namespace Foo.Bar.
end Foo.Bar.

namespace Foo.
  namespace Bar.
end Foo.Bar.

namespace Foo.
  namespace Bar.
  end Bar.
end Foo.
