include Core.

name n : message. name m : message.
abstract g : message -> message.

system null.

global lemma _ :
  Exists (f :_[adv]), [f n = n]. 
Proof. 
  exists fun (x:message) => x. 
  auto.
Qed.

global lemma _ (y : message -> message) :
  Exists (f :_[adv]), [f n = n]. 
Proof. 
  (* Note: global exists default to `si` *)
  checkfail exists fun (x:message) => diff(x,g x) exn Failure. (* not system indep *)

  checkfail exists fun (x:message) => y x         exn Failure. (* not adversarial *)

  exists fun (x:message) => x. 
  auto.
Qed.

global lemma _ (y : message -> message[adv]) : 
  Exists (f :_[const]), [f n = n]. 
Proof. 
  (* Note: global exists default to `si` *)
  checkfail exists fun (x:message) => diff(x,g x) exn Failure. (* not system indep *)

  checkfail exists fun (x:message) => y x         exn Failure. (* not constant *)

  exists fun (x:message) => x. 
  auto. 
Qed.

(* ---------------------------------------------- *)
global lemma _ (y : message -> message[adv]) : 
  Exists (f :_ -> message[const], g:_ -> message[const]), [f n = g n]. 
Proof. 
  (* Note: global exists default to `si` *)
  checkfail exists fun (x:message) => diff(x,g x) exn Failure. (* not system indep *)

  checkfail exists fun (x:message) => y x         exn Failure. (* not constant *)

  exists fun (x:message) => x. 
  exists fun (x:message) => x. 
  auto. 
Qed.
