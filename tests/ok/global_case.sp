(* check global case over timestamps: constant+si is necessary *)

channel c

namespace T.

  system (in(c,x);out(c,x) | !_i in(c,x);out(c,x)).

  global lemma _ (t:timestamp) :
    [t = init] \/ [t = A] \/ Exists (i:index), [t = A1(i)].
  Proof. 
    checkfail case t exn Failure. (* [t] not constant and si *)
  Abort.
  
  global lemma _ (t:timestamp[const]) :
    [t = init] \/ [t = A] \/ Exists (i:index), [t = A1(i)].
  Proof. 
    case t => ?.
    + by left. 
    + by right; left. 
    + right; right. 
      destruct H as [i _]. 
      by exists i.
  Qed.
end T.

(*------------------------------------------------------------------*)
namespace I.
  inductive t = A : int -> t | B : string -> t.
  
  global lemma _ @system:any (t:t) :
    (Exists (i:int), [t = A i]) \/ (Exists (s:string), [t = B s]).
  Proof. 
    checkfail case t exn Failure. (* [t] not constant and si *)
  Abort.
  
  global lemma _ @system:any (t:t[const]) :
    (Exists (i:int), [t = A i]) \/ (Exists (s:string), [t = B s]).
  Proof.
    case t => x.
    + by left; exists x.
    + by right; exists x.
  Qed.
end I.
