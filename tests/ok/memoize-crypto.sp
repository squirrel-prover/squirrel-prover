include Core.

channel c.

type key.
type rand.

op enc : message -> rand -> key -> message.
op dec : message -> key -> message.

game CCA2 = {
  rnd key : key;
  var log = empty_set;

  oracle lr m0 m1 = { 
    rnd r : rand;
    var e = enc (diff(m0,m1)) r key;
    log := add e log;
    return e; 
  }

  oracle dec c = {
    return if not (mem c log) then dec c key else witness;
  }
}.

op format ['a] : 'a -> message.

name k : key.
name r : rand.

action A : 0.
action B : 0.
 
system P = 
  A: in(c,x); out(c, enc (diff(x,empty)) r k) |
  B: in(c,y);
     out(c, format (if A < B && y = enc (diff(input@A,empty)) r k
                    then witness
                    else dec y k)).

global lemma _ @system:P (t:_[adv]) :
  [happens t] -> equiv(frame@t).
Proof.
  intro Hap.

  (* Without `~time_sensitive`, if `A < B`, the decryption `dec x k`
     in B's output is not guarded by `x <> enc diff(input@A,empty)`, but
     `crypto` does not realize that it does not need it. We are
     stuck, and cannot conclude. *)
  checkfail by crypto CCA2 => // exn GoalNotClosed.

  crypto ~time_sensitive CCA2 => //. 
Qed.

global lemma _ @system:P (t:_[adv]) :
  [happens t] -> [happens A] -> 
  equiv(frame@t, enc (diff(input@A,empty)) r k).
Proof.
  intro Hap HapA.

  (* Without `~time_sensitive`, if `A < B`, the decryption `dec x k`
     in B's output is not guarded by `x <> enc diff(input@A,empty)`, but
     `crypto` does not realize that it does not need it. We are
     stuck, and cannot conclude. *)
  checkfail by crypto CCA2 => // exn GoalNotClosed.

  crypto ~time_sensitive CCA2 => //. 
Qed.
