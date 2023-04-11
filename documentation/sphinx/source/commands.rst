.. _section-commands:

=========
Commands
=========

**TODO**

- describe the (few) commands available in Squirrel;
- `Proof`, `Qed`, `Abort`, `Reset`... are also commands.

.. cmd:: Proof

  Enter proof mode with a unique subgoal
  corresponding to the previous unproved :n:`@goal`.

.. cmd:: Qed

   Close the current :n:`@goal` if it's completed.

.. cmd:: Abort

   Abort the current proof.

.. cmd:: undo {? @natural}

   Undo the :n:`@natural` (default 1) last sentence(s). 
   Concretely takes :n:`@natural`:math:`^{th}` previous prover state
   as the current one.

   In general :cmd:`undo` commands are not used in `Squirrel` scripts but used for
   `Proof-General <https://proofgeneral.github.io/>`_ navigation.

.. cmd:: Reset

   Reset the prover state. This command can be undone with :cmd:`undo` since it does not clear
   the history of state.

.. cmd:: set @identifier = {| @bool | @natural }

   Set any squirrel option using its :n:`@identifier`:

   ====================== ============================================ ======================
   Option identifier      Description                                  Default value
   ====================== ============================================ ======================
   timeout                timeout for the solver in seconds.           2
   printTRSEquations      Print equations of the TRS system            false
   debugConstr            Debug information for the constraint checker false
   debugCompletion        Debug information for the completion checker false
   debugTactics           Debug information for tactics                false
   processStrictAliasMode Strict alias mode for processus              false
   showStrengthenedHyp    Show hypothesis after strengthening          false
   autoIntro              Automatic introductions                      false
   autoFADup              Automatic FA Dup                             true
   newInduction           New equivalence induction principle (FIXME)  false
   postQuantumSound       Post-quantum soundness                       false
   ====================== ============================================ ======================

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

.. cmd:: search @pattern {? in [{| @system_id | @system_exp }] }

   Search lemmas containing a given :n:`@pattern`. 
   A :n:`{| @system_id | @system_exp }` can be specified otherwise it is searched in the :n:`@global`
   system.

  .. example:: searching axioms with included patterns

    .. squirreltop:: in

        axiom [any] bar1 ['a] : exists (x : 'a), true.
        axiom [any] bar2 ['a] : exists (x : 'a -> 'a), true.

    .. squirreltop:: all

        search exists (x : _), _.
        search exists (x : _ -> _), _.
