include Core.


abstract a : message.
abstract b : message.
abstract ok: message.
game FOO = {
var list = empty_set;
oracle foo = {
list := add ok list;
return if mem ok list then diff(a,b) else zero
}}.




system null.


(*Abstract list are over approximation, we cannot conclude mem *)
global lemma _ : equiv(diff(a,b)).
Proof.
checkfail crypto FOO exn Failure.
Abort.
