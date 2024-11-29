channel c.

op a : message.
op b : message.

system P = A:out(c,diff(a,b)).

global lemma _ 
  @system:P
: 
  [happens A] ->
  Let x = diff(output@A,output@A) in
  equiv(x = diff(b,b)).
Proof. 
  intro H x. 
  trans [P/right,P/right]. 
  + rewrite /x. (* we are in `P`, thus we can unfold `x` here *)
    admit.      
   (* the goal is false though (this does not matter, as this is not
      what we are trying to test here. *)

  + 
   (* We are in `(left:P/right, right:P/right)`.
      `x` is a biterm defined in `(left:P/left, right:P/right)` to be

        `left  ↦ output{P/left}@A`
        `right ↦ output{P/right}@A`

      Thus, `x` could be unfolded here into:
      
        `diff(output{P/left}@A, output{P/right}@A)`

      which is `diff(a,b)`, and **not** `diff(b,b)`!. *) 
     checkfail auto exn GoalNotClosed. 
     checkfail by rewrite /x exn Failure. 
     (* remark that the precise reasons why these tests fails may
        change *)
     admit.

  + admit.                      (* we do not care about this last case *)
Qed.
