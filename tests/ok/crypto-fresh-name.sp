include Basic.

set verboseCrypto = true.

abstract a:message.
abstract b:message.
abstract h: message -> message -> message ->  message.

game FOO = {
oracle foo  = {
rnd r:message;
rnd k:message;
return  h r k (diff(a,b))
}
}.


channel c.
name n : message.
name m : message.

process A = 
let m = h n n diff(a,b) in 
out(c,m).

system Foo = A.

global lemma [Foo] _ (t:timestamp[const]):
[happens(t)]  -> equiv(frame@t).
Proof.
intro H.
crypto FOO => //.
* assert (A <= t && A <= t => false) as Hfalse by admit.
  apply Hfalse.
Qed.
