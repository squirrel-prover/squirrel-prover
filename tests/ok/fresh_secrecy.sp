include WeakSecrecy.

name n:message.

abstract m:message.
abstract p:message.
abstract q:message.

system P = null.


global lemma[set:P; equiv:none] test1:
  $(zero *> m) ->  $(n *> m).
Proof.
  intro H.
  fresh 0.  
  assumption.
Qed.

global lemma[set:P/left; equiv:none] test2:
  $(zero *>{[P]} m) ->  $(n *>{[P]} m).
Proof.
  intro H.
  fresh 0.  
  assumption.
Qed.

global lemma[set:P/left; equiv:none] test3:
  $(n *>{[P]} n).
Proof.
  fresh 0.
  checkfail auto exn GoalNotClosed.
Abort.

global lemma[set:P; equiv:none] test4:
  $(n *>{[P/left]} n).
Proof.
  fresh 0.
  checkfail auto exn GoalNotClosed.
Abort.


global lemma[set:P; equiv:none] test5:
  $((m,p) *> q) ->  $((m,n,p) *> q).
Proof.
  intro H.
  fresh 1.  
  assumption.
Qed.


global lemma[set:P; equiv:none] test6:
  $((m,p) *> n).
Proof.
  fresh.  
Qed.

global lemma[set:P; equiv:none] test7:
  $((m,n,p) *> n).
Proof.
  fresh.  
  checkfail auto exn GoalNotClosed.
Abort.


