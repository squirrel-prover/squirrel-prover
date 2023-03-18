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

TODO make pattern/system links to their definitions

.. tacn:: cs @pattern {? in @system}
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

   .. exn:: Argument of cs should match a boolean
      :undocumented:

   .. exn:: did not find any conditional to analyze
      :undocumented:
