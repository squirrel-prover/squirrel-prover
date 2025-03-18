include Core.

abstract h : message -> message.
abstract foo:message.
abstract oof:message.

game FOO1 = {
  rnd key : message;
  oracle test x = { 
   return if h(x) = h(zero) then diff(foo,oof)} 
}.

game FOO2 =  {
  rnd key : message;
  oracle test = {
   return if h(key) = h(zero) then diff(foo,oof)}
  
}. 


game FOO3 =  {
  oracle test = {
   rnd r : message;
   return if r = h(zero) then diff(foo,oof)}
  
}. 


system null.


abstract x:message.

global lemma _ : [h(witness) = h(zero)] -> equiv(diff(foo,oof)).
Proof.
intro *.
crypto FOO1.
auto.
Qed.

name r :message.

global lemma _ : [h r = h zero] -> equiv(diff(foo,oof)).
Proof.
intro *.
checkfail crypto ~no_subgoal_on_failure FOO2 exn Failure.
crypto FOO2 (key:r).
auto.
Qed.


global lemma _ : equiv(diff(foo,oof)).
Proof.
checkfail crypto ~no_subgoal_on_failure FOO3 exn Failure.
Abort.
