include Basic.

game ALEA = {
rnd key : message;
oracle sample = { 
rnd r :message;
return  <r,key> }
}.

channel c
name n : index -> message.
name m : index -> message.

abstract f : message -> message.
      
op g x = <f x, f x>.

system [T] (S : !_i !_j new n; out(c,n)).

global lemma [T] _ (i,j:index[adv]) : equiv(
seq(k:index => <n(k),m(i)>), <n(j),m(i)>). 
Proof.
crypto ALEA => //.
Qed.

global lemma [T] _ (i,j,k:index[adv]) : equiv(
<n(k),m(i)>,<n(j),m(i)>).
Proof.
crypto ALEA.
checkfail auto exn GoalNotClosed.
Abort.


global lemma [T] _ (i,j:index[adv]) (b:bool): equiv(
if b then <n(i),m(j)> else <n(i),m(j)>).
Proof.
checkfail crypto ALEA exn Failure.
Abort.



global lemma [T] _ (i,j,k,l:index[adv]) :
[l=k && j <> i && j<>l && i<>l] -> 
equiv( <n(i),n(k)>,<n(j),n(l)>).
Proof.
intro H.
crypto ALEA => //.
Qed.


global lemma [T] _ (i,j,k,l:index[adv]) :
[l=k && j<>l && i<>l] -> 
equiv( <n(i),n(k)>,<n(j),n(l)>).
Proof.
intro H.
crypto ALEA => //.
checkfail auto exn GoalNotClosed.
Abort.

global lemma [T] _ (i,j,k,l:index[adv]) :
[l=k && j <> i && i<>l] -> 
equiv( <n(i),n(k)>,<n(j),n(l)>).
Proof.
intro H.
crypto ALEA => //.
checkfail auto exn GoalNotClosed.
Abort.

global lemma [T] _ (i,j,k,l:index[adv]) :
[l=k && j <> i && j<>l] -> 
equiv( <n(i),n(k)>,<n(j),n(l)>).
Proof.
intro H.
crypto ALEA => //.
checkfail auto exn GoalNotClosed.
Abort.

global lemma [T] _ (i,j,k,l:index[adv]) :
[j <> i && j<>l && i <> k] -> 
equiv( <n(i),n(k)>,<n(j),n(l)>).
Proof.
intro H.
crypto ALEA => //.
checkfail auto exn GoalNotClosed.
Abort.

global lemma [T] _ (i,j,k,l:index[adv]) :
[k <> j && j <> i && j<>l && i <> k] -> 
equiv( <n(i),n(k)>,<n(j),n(l)>).
Proof.
intro H.
crypto ALEA => //.
checkfail auto exn GoalNotClosed.
Abort.

global lemma [T] _ (i,j,k,l:index[adv]) :
[k <> j && j <> i && j<>l && i <> k && i<> l] -> 
equiv( <n(i),n(k)>,<n(j),n(l)>).
Proof.
intro H.
crypto ALEA => //.
Qed.


global lemma [T] _ :
equiv(
seq (k:index => <n(k),m(k)>)).
Proof.
crypto ALEA.
checkfail auto exn GoalNotClosed.
Abort.

global lemma [T] _ (i:index[adv]) : 
equiv( seq( k : index =>  <n(k),m(i)>)).
Proof.
crypto ALEA => //.
Qed.


abstract h : index -> index.



global lemma [T] _ (i:index[adv]) : 
equiv( seq( k : index =>  <n(h(k)),m(i)>)).
Proof.
crypto ALEA => //.
checkfail auto exn GoalNotClosed.
Abort.


(*n(j) is seen as a global name : the second compnent is then a game compuation*)
global lemma [T] _ (i,j,k,l : index[adv]) (b:bool[adv]) :
[k<>j && l <> i && l <> j] -> 
equiv( if b then <n(k),n(j)> else <n(l), n(i)> ).
Proof.
intro H.
crypto ALEA => //.
Qed.


global lemma [T] _ (i,k:index[adv]):
[i <> k] ->
equiv( seq (x:index => <n (i), n(k)>)).
Proof.
intro H.
crypto ALEA.
auto.
checkfail auto exn GoalNotClosed.
Abort.

global lemma [T] _ (i,k:index[adv]):
[i <> k ] ->
equiv(<m(i),m(k)>, seq (x:index => <n (x), m(k)>)).
Proof.
intro H.
crypto ALEA => //.
Qed.
