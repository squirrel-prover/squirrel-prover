.. _section-commands:

=========
Commands
=========

.. cmd:: Proof

  Enter proof mode with a unique subgoal
  corresponding to the previous unproved :n:`@goal`.

.. cmd:: Qed

   Close the current :n:`@goal` if it's completed.

.. cmd:: Abort

   Abort the current proof.

.. cmd:: undo {? @natural}

   :g:`undo n` undo the :g:`n` (default 1) last sentence(s). 
   Concretely takes :g:`n`:math:`^{th}` previous prover state
   as the current one.

   In general :cmd:`undo` commands are not used in `Squirrel` scripts but used for
   `Proof-General <https://proofgeneral.github.io/>`_ navigation.

.. cmd:: Reset

   Reset the prover state. This command can be undone with :cmd:`undo` since it does not clear
   the history of state.

.. cmd:: Include @file

   Loads the theories/:n:`@file`.sp. 

     .. example:: Including theories/Basic.sp

       .. squirreldoc::

          include Basic.

   If you
   install squirrel (with ``make install``) and not running it from root directory of its
   sources, this directory is located in ``~/.local/bin``.


   
.. cmd:: set @identifier = {| @bool | @natural }

   Set any squirrel :gdef:`option` using its :n:`@identifier`:

   ====================== ============================================ ======================
   Option identifier      Description                                  Default value
   ====================== ============================================ ======================
   timeout                Timeout for the solver in seconds            2
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
  :g:`print` without :n:`@idendifier` shows the current system.

  .. example:: printing a goal

    .. squirreltop:: in

        goal [any] foo : true.
        Proof.
          admit.
        Qed.

    .. squirreltop:: all

        print foo.

.. cmd:: search @term {? in [{| @system_id | @system_exp }] }

   Search lemmas containing a given :n:`@term` (that can contains
   holes ``_`` as specified in :n:`@sterm`). 
   A :n:`{| @system_id | @system_expr }` can be specified otherwise it is searched in :n:`@any`
   systems.

  .. example:: searching axioms with included patterns

    .. squirreltop:: in

        axiom [any] bar1 ['a] : exists (x : 'a), true.
        axiom [any] bar2 ['a] : exists (x : 'a -> 'a), true.

    .. squirreltop:: all

        search exists (x : _), _.
        search exists (x : _ -> _), _.


.. cmd:: hint rewrite @identifier

  Add a rewriting rule from the lemma :n:`@identifier` to the
  user-defined rewriting database. The lemma should establish a local
  formula consisting of a universally quantified conditional equality.
  In other words, it should essentially be of the form
  :n:`forall @binders, phi_1 => ... => phi_n => u = v`.

  The goal will be used to rewrite occurrences of :n:`u` into the
  corresponding occurrences of :n:`v`, assuming the conditions
  :n:`phi_1, ..., phi_n` reduces to :n:`true` (using :ref:`reduction`).

  .. example:: add rewriting rule

    .. squirreldoc::

        axiom [any] and_true_l (b : boolean) : (true && b) = b.
        hint rewrite and_true_l.

