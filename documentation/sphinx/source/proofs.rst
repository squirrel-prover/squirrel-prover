.. _section-proofs:

.. How to write proofs in Squirrel

------
Proofs
------

The proof of a goal is given after the goal
between the ``Proof.`` and ``Qed.`` markers.
It consists in a list of tactics. The invokation of each
tactic modifies the proof state, which contains a list of goals to prove.
Initially, the proof state consists a single goal, as declared by the
user. Then each tactic reduces the first goal of the proof state to
an arbitrary number of new subgoals. When no goal is left, the proof
is completed and ``Qed.`` can be used.

Tacticals
---------

**TODO** I'm not sure we want to document tacticals using the same
role as elementary tactics, I did it like this for now just so the
references to try and repeat in the appendix work.

.. tacn:: nosimpl @tactic

  Call tactic without the subsequent implicit use of simplications.
  This can be useful to understand what's going on step by step.
  This is also necessary in rare occasions where simplifications are
  actually undesirable to complete the proof.

.. tacn:: try @tactic

  Try to apply the given tactic. If it fails, succeed with the
  subgoal left unchanged.

.. tacn:: repeat @tactic

  Apply the given tactic, and recursively apply it again on the
  generated subgoals, until it fails.

Tactics
-------

Automatic simplifications
-------------------------

**TODO** document what is done implicitly after each tactic invokation,
clarify that this is not the same as calling the `simpl` tactic.

Tactic arguments
~~~~~~~~~~~~~~~~

In the context of a (sub)goal, an :gdef:`assumption` refers to
an hypothesis in the current goal,
a previously proved goal, or
a previously declared axiom.
Assumptions are referred to by their identifier when used in
tactics.

.. prodn::
  assumption ::= @identifier

Tactics that apply to equivalence goals may take a natural number
as argument to identify one item in the equivalence. This is represented
using the :token:`position` token.

.. prodn::
  position ::= @natural

**TODO** most (all?) tactics take terms and formulas as patterns,
with an implicit filling of the holes by matching against the subgoal's
conclusion; document this, and also decide whether arguments are shown
as :token:`term`, :token:`formula`, :token:`pattern`,
:token:`formula_pattern`, etc.

Proof terms
~~~~~~~~~~~

Proof terms are used by several tactics as a convenient way to combine
and (partially) apply :term:`assumptions <assumption>` in order to
derive new facts.

.. prodn::
   proof_term ::= @assumption {? @pt_arg}

.. prodn::
   pt_arg ::= @assumption | @sterm | (% @proof_term)

Note that the grammar for proof term arguments :token:`pt_arg` is
ambiguous (because of the :token:`assumption` and :token:`sterm`
productions). When this happens, Squirrel tries to desambiguate using
the context.

.. note::
   The :n:`(% @proof_term)` syntax is experimental, and is subject to
   change in the future.

TODO

.. _reduction:

Reduction
~~~~~~~~~

Several tactics (e.g., :tacn:`simpl` and :tacn:`auto`) rely on an
reduction engine. This engine repeatedly applies several
transformations, corresponding to the following flags.

.. prodn:: simpl_flags ::= ~flags:[ {*, {| rw | beta | proj | delta | constr } } ]

Leaving the flags unspecified results in the :n:`rw`, :n:`beta` and
:n:`proj` transformations being used. Specifying an empty list of
flags results in no transformations being applied. Otherwise, only the
specified transformations are applied, as described next:

  - :n:`rw`: perform user-defined rewriting;
  - :n:`beta`: perform beta-reductions;
  - :n:`proj`: compute tuple projections;
  - :n:`delta`: replace macros and operators by their definitions;
  - :n:`constr`: automatically simplify trace formulas using
    constraint reasoning.

The :n:`constr` transformation replaces trace (sub)formulas that
are provably equal to :n:`true` or :n:`false` by this value.
When doing so, the constraint solver takes into account
the current hypotheses but also the conditionals that surround
the trace formula.

The user-defined rewriting transformation eagerly applies the rewrite
rules added to the rewriting database using the :cmd:`hint rewrite`
command.

Common errors
~~~~~~~~~~~~~

.. exn:: Out of range position.

     Argument does not correspond to a valid equivalence item.

Common tactics
~~~~~~~~~~~~~~

.. tacn:: reduce {? @simpl_flags}

     Reduce all terms in a subgoal, working on both hypotheses and conclusion.
     
     This tactic always succeeds, replacing the initial subgoal with a
     unique subgoal (which may be identical to the initial one).

     The tactic uses the :ref:`reduction engine <reduction>`
     with the provided flags.

.. tacn:: simpl {? @simpl_flags}

     Simplify a subgoal, working on both hypotheses and conclusion.
     This tactic always succeeds, replacing the initial subgoal with
     a unique simplified subgoal.

     The tactic uses the :ref:`reduction engine <reduction>`
     with the provided flags.

     When the conclusion of the goal is a conjunction, the tactic
     will attempt to automatically prove some conjuncts (using :tacn:`auto`)
     and will then return a simplified subgoal without these conjuncts.
     In the degenerate case where no conjunct remains, the conclusion
     of the subgoal will be :n:`true`.

     When the conclusion of the goal is an equivalence, the tactic
     will automatically perform :tacn:`fa` when at most one of the remaining
     subterms is non-deducible. It may thus remove a deducible item
     from the equivalence, or replace an item :n:`<u,v>` by :n:`u`
     if it determines that :n:`v` is deducible.

.. tacn:: auto {? @simpl_flags}

     Attempt to automatically prove a subgoal.

     The tactic uses the :ref:`reduction engine <reduction>`
     with the provided flags.

     Moreover, for local goals, the tactic relies on basic
     propositional reasoning, rewriting simplications, and both
     :tacn:`constraints` and :tacn:`congruence`.

     .. exn:: cannot close goal
        :name: _goalnotclosed

        The current goal could not be closed.

.. tacn:: congruence

     Attempt to conclude by automated reasoning on message (dis-)equalities.
     Equalities and disequalities are collected from hypotheses, both local 
     and global, after the destruction of conjunctions (but no case analyses 
     are performed to handle conjunctive hypotheses). If the conclusion
     is a message (dis-)equality then it is taken into account as well.

.. tacn:: constraints

     Attempt to conclude by automated reasoning on trace literals.
     Literals are collected from hypotheses, both local and global,
     after the destruction of conjunctions (but no case analyses are
     performed to handle conjunctive hypotheses). If the conclusion
     is a trace literal then it is taken into account as well.

Equivalence tactics
~~~~~~~~~~~~~~~~~~~

.. tacn:: cs @pattern {? in @position}
   :name: case_study

   Performs case study on conditionals inside an equivalence.

   Without a specific target, ``cs phi`` will project all conditionals
   on phi in the equivalence. With a specific target, ``cs phi in i``
   will only project conditionals in the i-th item of the equivalence.

   .. example::

     When proving an equivalence
     ``equiv(if phi then t1 else t2, if phi then u1 else u2)``
     invoking ``cs phi`` results in two subgoals:
     ``equiv(phi, t1, u1)`` and ``equiv(phi, t2, u2)``.

   .. exn:: Argument of cs should match a boolean.
      :undocumented:

   .. exn:: Did not find any conditional to analyze.

        some doc

.. tacn:: prf @position
   :name: prf

   TODO why optional message in Squirrel tactic; also fix help in tool

.. tacn:: fresh @position
   :name: fresh

   TODO

.. tacn:: fa {@position | @term}
   :name: fa

   TODO
