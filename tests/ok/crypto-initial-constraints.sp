include Basic.

name n : index -> index.
name m : index -> message.

abstract a : index.
abstract b : index.

game EMPTY = {
rnd key : message;
}


system null.


global lemma _ : 
equiv( n a).
Proof.
checkfail (crypto EMPTY (key: m (diff(a,b)))) exn Failure.
Abort.

global lemma _ (i:index[adv]) :
equiv(n a).
Proof.
crypto EMPTY (key: m i).
Qed.

global lemma _ (i:index[adv]):
equiv(n a).
Proof.
crypto EMPTY (key: m (n i)).
Qed.

abstract h : message* message -> index.
name k : index -> message.
name k2 : message.

game HASH = {
rnd key : message;
oracle hashing (m:message) ={ return h(m,key)}}.

global lemma _ (i:index[adv]):
[false] -> equiv( h(m(i),k2)).
Proof.
intro H.
crypto HASH (key: k (h(zero,k2))).
auto.
Qed.
