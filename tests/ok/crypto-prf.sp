include Basic.

abstract h : message*message -> message.

game PRF = {
  rnd key : message;
  var lhash = empty_set;
  var lchal = empty_set;

  oracle ohash x = {
    lhash := add x lhash;
    return if mem x lchal then zero else h(x,key) 
  }

  oracle challenge x = {
    rnd r : message;
   (* the list before update *)
    var old_lchal = lchal;
    lchal := add x lchal;

    return if mem x old_lchal || mem x lhash  then zero else diff(r, h(x,key))
  }
}.

name key    : index -> message
name nT     : index * index -> message.
name dummy  : index -> message.
name dummy' : index * index -> message.

system null.

(* Sequence of calls for hash oracle, followed by challenge. *)
global lemma _ (i,j:index[adv]) : 
  equiv(seq(k:index => h(dummy(k),key(i))),
        diff(dummy'(i,j),h(nT(i,j),key(i)))).
Proof.
  crypto PRF => //.
Qed.

(* Can't call hash oracle after challenge on same input. *)
global lemma _ (i:index[adv]) :
  equiv(diff(dummy(i), h(nT(i,i),key(i))),
        h(dummy(i),key(i))).
Proof.
  crypto PRF (key : key i).
  checkfail auto exn GoalNotClosed.
Abort.

(* Can't call challenge after hash oracle on same input. *)
global lemma _ (i:index[adv]) :
  equiv(h(dummy(i),key(i)),
        diff(dummy(i), h(nT(i,i),key i))).
Proof.
  crypto PRF (key : key i).
  checkfail auto exn GoalNotClosed.
Abort.

(* Current limitation: our treatment of invariants is not precise
   enough for the next example. Rephrasing the example as a protocol
   doesn't solve the issue. *)
global lemma _ (i:index[adv]) :
  equiv(seq(k:index => diff(dummy'(i,k),h(nT(i,k),key(i))))).
Proof.
  crypto PRF => //.
  checkfail auto exn GoalNotClosed.
Abort.
