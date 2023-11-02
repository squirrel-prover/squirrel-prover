(* We show in this file how the `crypto` tactic on the IND-CPA game
   can support applications which are beyond the reach of the current
   `cca1` tactic. *)

include Basic.

(* Defining an encryption function as an abstract function. *)
abstract enc : message -> message -> message -> message.

(* CPA game for our encryption function.
   It states the indistinguishability between
   the encryption of any message x and
   the encryption of a message of same size but with only 0 bits.*)
game CPA = {
  rnd key : message;
  oracle enc x = {
  rnd r : message;
  return enc (diff(x,zeroes x)) r key
  }
}.

(* A very simple bi-protocol with many sessions of a process that outputs
   - on the left: the encryption of some random message `foo`;
   - on the right: the encryption of a zeroed-out version of that message. *)
name k :  message.
channel c.
process foo (i:index) = 
  new foo;
  new n;
  out(c,diff((enc foo n (k)), (enc (zeroes foo) n (k)))).

system (!_i F : foo(i)).

(* Proof of indistinguishability for the two projection of the system.
   The `crypto` tactics handles induction, and can thus prove indistinguishability
   for all frames. Proving such goals can be useful to support rewriting a system
   into a variant system, to reduce the proof on one protocol to a proof of
   the same property on another, simple protocol. *)
global lemma _ (t:timestamp[const]) : [happens(t)] -> equiv(frame@t).
Proof.
  intro H.
  crypto CPA (key : k) => //.
Qed.

(* Another use where `crypto` handles many diffs at a time,
   which e.g. the current `cca1` tactic does not support. *)
abstract msg : index -> message.
name key : message.
name rand : index -> message.
global lemma _ : equiv(fun i => enc (diff(msg i, zeroes (msg i))) (rand i) key).
Proof.
  crypto CPA (key : key) => //.
Qed.
