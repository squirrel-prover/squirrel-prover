(* Checks oracle call in the right order*)

include Basic.

abstract ok : message * message * message * message -> message.
abstract ko : message.
abstract a : message.
abstract b: message.


game FOO = {
rnd key : message;
var l = empty_set;
oracle call x y ={
var old_l = l;
l := add y l;
return if mem y old_l then ko else ok(x,y,key,diff(a,b)) 
}
}.

system null.
name m : message.
name n : message.
name k : message.

global lemma _  : 
[m<>m] -> 
equiv( ok( (ok(m,m,n,diff(a,b))) ,m,n ,diff(a,b) )).
Proof.
intro H.
crypto FOO.
auto.
Qed.

