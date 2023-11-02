include Basic.

abstract a : message.
abstract b : message.
abstract ok : message.
abstract ko : message.

game FOO = {
var l = empty_set;
oracle foo x = {
l:= add a l;
return if mem x l then diff(ok,ko) else ko}}.

game FOO2 = {
var l = empty_set;
oracle foo x = {
l:= add diff(a,b) l;
return if mem x l then x else ko}}.

system null.


global lemma _ : equiv(diff(ok,ko)).
Proof.
checkfail crypto FOO exn Failure.
Abort.

game FOO3 = {
var b = empty_set;
oracle foo = {
var old_b = b;
b := add a b;
return if mem a old_b then zero  else diff(ok,ko)
}}.

global lemma _ : equiv(diff(ok,ko)).
Proof.
crypto FOO3.
Qed.



(*FIXE ME : infinite loop on this terms.*)
(* global goal _ : equiv(diff(a,b)). *)
(* Proof. *)
(* crypto FOO2. *)
