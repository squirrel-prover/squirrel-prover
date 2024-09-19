include Basic.

game FOO = {}.


system null.

abstract a: message.
abstract b: message.

global lemma _ : 
equiv(diff(a,b)).
Proof.
checkfail crypto FOO exn Failure.
Abort.



global lemma _ : 
equiv(fun (x:message) => x).
Proof.
crypto FOO.
Qed.


global lemma _ : 
equiv(fun (x:message) => (x,diff(a,b))).
Proof.
checkfail crypto FOO exn Failure.
Abort.


abstract h: message -> message.
global lemma _ : 
equiv(fun (x:message) => h x, h diff(a,b)).
Proof.
checkfail crypto FOO exn Failure.
Abort.
