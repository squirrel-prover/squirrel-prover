.. _section-commands:

=========
Commands
=========

**TODO**

- describe the (few) commands available in Squirrel;
- `Proof`, `Qed`, `Abort`, `Reset`... are also commands.

.. cmd:: Proof

  Enter proof mode with a unique subgoal
  corresponding to the previous unproved goal.

.. cmd:: Qed

   Close the current goal if it's completed.

.. cmd:: Abort

   Abort the current proof.

.. cmd:: undo

   Undo the last sentence. Concretely takes the previous prover state
   as the current one.

.. cmd:: Reset

   Reset the prover state. This command can be undone with :cmd:`undo` since it does not clear
   the history of state.

.. cmd:: print {? @identifier}

  Shows definition of given :n:`@identifier` if it is a lemma, function, name, macro or system.
  :g:`print` without :n:`@idendifier` shows current system.

  .. example:: printing a goal

    .. squirreltop:: in

        goal [any] foo : true.
        Proof.
          admit.
        Qed.

    .. squirreltop:: all

        print foo.

.. cmd:: search @pattern {? in @system_id}

   Search lemmas containing a given :n:`@pattern`. 
   A :n:`@system_id` can be specified otherwise it is searched in the global
   system.

  .. example:: searching axioms with included patterns

    .. squirreltop:: in

        axiom [any] bar1 ['a] : exists (x : 'a), true.
        axiom [any] bar2 ['a] : exists (x : 'a -> 'a), true.

    .. squirreltop:: all

        search exists (x : _), _.
        search exists (x : _ -> _), _.
