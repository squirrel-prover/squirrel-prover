(* Test that a number of global case disjunction over [ϕ ∨ ψ] succeed
   when one of ϕ or ψ is constant. 

   Thus, this files mostly checks that Squirrel correctly check
   constancy. *)

include Core.
include "Data/List.sp".

abstract att1 : list int -> bool.
abstract att2 : (list int -> message) -> bool.
abstract att3 : (int -> message) -> bool.

op a : bool.
op b : bool.

system default = null.

global lemma _ : [false].
Proof.
ghave [ Cdom | Cdom ] :
[
    (att1 (Cons 1 Nil))
    ||
    (att1 (Cons 1 Nil))
].

ghave [ Cdom | Cdom ] :
    [
    (att3 (fun (lf1:int) => zero))
    ||
    (att3 (fun (lf1:int) => zero))
    ].

ghave [ Cdom | Cdom ] :
    [
    (att2 (fun (lf1:list int) => zero))
    ||
    (true)
    ].

ghave [ Cdom | Cdom ] :
    [
    (true)
    ||
    (att2 (fun (lf1:list int) => zero))
    ].

ghave [ Cdom | Cdom ] :
    [
    (att2 (fun (lf1:list int) => zero))
    || 
    (att2 (fun (lf1:list int) => zero))
    ].
Abort.
