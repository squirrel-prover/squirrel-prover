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

:gdef:`Proof terms <proof term>`
are used by several tactics as a convenient way to
combine :term:`assumptions <assumption>` in order to derive new
facts that may be used in various ways.

TODO

.. _autosimpl:

Simplification engine
~~~~~~~~~~~~~~~~~~~~~

Several tactics (e.g., `simpl`_ and `auto`_) rely on an automatic
simplification engine. This engine repeatedly applies several
transformations, corresponding to the following flags.

.. prodn::
  simpl_flags ::= ~flags:[{*, {| beta | proj | delta | constr}}]

Leaving the flags unspecified results in all simplifications
being used. Specifying an empty list of flags results in no
simplification being applied. Otherwise, only the specified
transformations are applied, as described next:

- :n:`rewrite`: perform user-defined rewriting;
- :n:`delta`: replace macros and operators by their definitions;
- :n:`beta`: perform beta-reductions;
- :n:`proj`: compute projections;
- :n:`constr`: automatically simplify trace formulas using
  constraint reasoning.

The :n:`constr` simplification replaces trace (sub)formulas that
are provably equal to ``true`` or ``false`` by this value.
When doing so, the constraint solver takes into account
the current hypotheses but also the conditionals that surround
the trace formula.

The user-defined rewriting simplification corresponds to eagerly
applying the rewrite rules corresponding to the lemmas added
to the rewriting database using the `hint rewrite`_ command.

.. cmd:: hint rewrite @identifier

  Add lemma :n:`@identifier` to the user-defined rewriting database.
  The lemma should establish a local formula consisting of
  a universally quantified conditional equality.
  In other words, it should essentially be of the form
  ``forall ..., phi_1 => ... => phi_n => u = v``.

  The goal will be used to rewrite occurrences of ``u`` into
  the corresponding occurrences of ``v``. When this happens,
  the conditions ``phi_1, ..., phi_n`` will be added as subgoals.
  Note that rewriting is solely controlled by pattern-matching
  against ``u``; there is no way to restrict it based on the
  provability of the conditions ``phi_i``. Hence one should
  be careful not to enter rewriting lemmas with a too general
  left-hand side ``u``.

Common errors
~~~~~~~~~~~~~

.. exn:: Out of range position.

     Argument does not correspond to a valid equivalence item.

Common tactics
~~~~~~~~~~~~~~

.. tacn:: auto {? simpl_flags}

     Attempt to automatically prove a subgoal.

     The tactic uses the :ref:`simplification engine <autosimpl>`
     with the provided flags.

     For local goals, the tactic relies on basic propositional reasoning,
     rewriting simplications, and both `constraints`_ and `congruence`_.


.. tacn:: congruence

     Attempt to conclude by automated reasoning on message (dis)equalities.
     Equalities and disequalities are collected from hypotheses, both local 
     and global, after the destruction of conjunctions (but no case analyses 
     are performed to handle conjunctive hypotheses). If the conclusion
     is also a message (dis)equality then it is taken into account as well.

.. tacn:: constraints

     Attempt to conclude by automated reasoning on trace literals.
     Literals are collected from hypotheses, both local and global,
     after the destruction of conjunctions (but no case analyses are
     performed to handle conjunctive hypotheses). If the conclusion
     is also a trace literal then it is taken into account as well.

.. tacn:: simpl {? simpl_flags}

     Simplify a subgoal, working on both hypotheses and conclusion.
     This tactic always succeeds, replacing the initial subgoal with
     a unique simplified subgoal (which may be identical to the
     initial one).

     The tactic uses the :ref:`simplification engine <autosimpl>`
     with the provided flags.

     When the conclusion of the goal is a conjunction, the tactic
     will attempt to automatically prove some conjuncts (using `auto`_)
     and will then return a simplified subgoal without these conjuncts.
     In the degenerate case where no conjunct remains, the conclusion
     of the subgoal will be ``true``.

     When the conclusion of the goal is an equivalence, the tactic
     will automatically perform ``fa`` when at most one of the remaining
     subterms is non-deducible. It may thus remove a deducible item
     from the equivalence, or replace an item ``<u,v>`` by ``u``
     if it determines that ``v`` is deducible.

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
