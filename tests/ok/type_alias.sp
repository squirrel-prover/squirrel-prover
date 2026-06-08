include Core.


type messpair = bool * message.


lemma [any] _ : forall t: messpair, exists u: bool * message, u=t.
Proof.
intro t.
by exists t. 
Qed.

lemma [any] _ : forall t:bool*message, exists u: messpair, u=t.
Proof.
intro t.
by exists t. 
Qed.


type order2 a = (a -> a) -> a.


abstract test : order2 message.

global lemma [any] _ : Exists (u:(order2 message) [adv]), [u=test].
Proof.
(* Check that `order2 message` is indeed detected as order 2 and thus
not adv. *) 
checkfail exists test exn Failure.  
Abort.


(* A few more definitions to test type unification and inference. *)

type act.

type protocol  = (act -> message -> message).

let empty_protocol : protocol = fun a r  => empty.

abstract dom : protocol -> act -> bool.

exact axiom [any] dom_true (S : protocol) :
     forall (ac : act), 
     dom S ac = true => forall m, S ac m <> empty.

exact axiom [any] dom_false (S : protocol) :
     forall (ac : act),
     dom S ac = false => forall m, S ac m = empty.
