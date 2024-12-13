include Core.

type seed[large].
type sk_enc[large].
type pk_enc.
type ctxt.
abstract pk_enc : sk_enc -> pk_enc.
abstract enc : message -> pk_enc -> seed -> ctxt.
abstract dec : ctxt -> sk_enc -> message.

abstract format : ctxt -> message.

name sk : sk_enc.
name seed : seed.
game CCA2 = {
rnd key : sk_enc;
var log = empty_set;
oracle encrypt (m0,m1 : message) = {
rnd seed: seed;
var c0 = enc m0 (pk_enc key) seed;
var c1 = enc m1 (pk_enc key) seed;
log := add (format diff(c0,c1)) log;
return diff(c0,c1)}

oracle decrypt (c : ctxt) = {
return if not (mem (format c) log) then dec c key
}
}.

system null.


global lemma apply_CCA2 (m0,m1 : message[adv])
 (c':ctxt[adv])
 (c : ctxt) :
[c = diff((enc m0 (pk_enc sk) seed),(enc m1 (pk_enc sk) seed))] ->
equiv(
c,if not (c=c') then dec c' sk
).
Proof.
intro Hc.
rewrite Hc.
crypto CCA2.
admit.
Qed.
