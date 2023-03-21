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

Tactics
-------

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

Proof terms
~~~~~~~~~~~

:gdef:`Proof terms <proof term>`
are used by several tactics as a convenient way to
combine :term:`assumptions <assumption>` in order to derive new
facts that may be used in various ways.

TODO

Common errors
~~~~~~~~~~~~~

.. exn:: out of range position

     Argument does not correspond to a valid equivalence item.

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

   TODO convention on capitalization for errors?
   Coq: capitalized + period.

   .. exn:: Argument of cs should match a boolean
      :undocumented:

   .. exn:: did not find any conditional to analyze

        some doc

.. tacn:: prf @position
   :name: prf

   TODO why optional message in Squirrel tactic; also fix help in tool

   .. exn:: out of range position

.. tacn:: fresh @position
   :name: fresh

   .. exn:: out of range position

     See :exn:`out of range position`
