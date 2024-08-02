include Basic.

abstract a : message.
abstract p : message -> bool.
abstract b0 : message.
abstract b1 : message.
abstract ok : message.
abstract ko : message.
abstract a0 : message.
abstract a1 : message.


game Foo = {
  var l = empty_set;

  oracle list = {
    l := add (if forall x, p x then ok else ko ) l;
    return diff(b0,b1)
  }

  oracle ab = {
    return if not (mem ok l) then diff(a0,a1)
  }
}.

system null.

global lemma _ : [ok <> if (forall (x:message), p x) then ok else ko] -> equiv(diff(b0,b1),diff(a0,a1)).
Proof.
  intro H.
  crypto Foo.
  assumption H.
Qed.
