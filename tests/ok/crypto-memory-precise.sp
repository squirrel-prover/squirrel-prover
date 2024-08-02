include Basic.

name n : index -> message.
abstract ok : message -> message.
hash h.

game FOO = {

rnd ki : message;
rnd ko : message;
var l = empty_set;
oracle ping m = {
l := add (ok m) l;
return h(m,ki);
}
oracle pong m = {
return if mem (ok m) l then zero else h(m,ko);
}

}.


name ka : message.
name kb : message.

system null.

global lemma _ :
equiv( seq (i:index =>
 <h((n i),ka),h(n(i),kb)>)).
Proof.
crypto FOO.
Abort.
