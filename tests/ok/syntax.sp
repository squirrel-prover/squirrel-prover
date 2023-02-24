(* some check on accepted syntax and type inference *)

(*==================================================================*)
(* quantifiers in lemmas *)

axiom [any] foo1 (x : message) : 
  exists (y,z : message, b : bool), 
    (x = y && y = z && z = x && b).

print foo1.

axiom [any] foo2 (x : message) : 
  exists (y,z,b : _), 
    (x = y && y = z && z = x && b).

print foo2.

axiom [any] foo3 (x : message) : 
  exists y z b, 
    (x = y && y = z && z = x && b).

print foo3.

(*------------------------------------------------------------------*)
axiom [any] _ (x : message) : 
  forall y z b, 
    (x = y && y = z && z = x && b).

(*------------------------------------------------------------------*)
axiom [any] _ (x : message) : 
  (fun y z b =>
     (x = y && y = z && z = x && b))
  = 
  (fun a b c => true).

axiom [any] _ (x : message) : 
  (fun y z b =>
     (x = y && y = z && z = x && b))
  = 
  (fun (_,_,_ : _) => true).

axiom [any] _ (x : message) : 
  (fun y z b =>
     (x = y && y = z && z = x && b))
  = 
  (fun _ _ _ => true).

(*==================================================================*)
(* operators *)

op bar1 (x : message) (y : message) (z : message) : bool = 
  x = y && y = z && z = empty.
print bar1.

op bar2 (x : _) (y : _) (z : _) : _ = (x = y && y = z && z = empty).
print bar2.

op bar3 x y z = (x = y && y = z && z = empty).
print bar3.
