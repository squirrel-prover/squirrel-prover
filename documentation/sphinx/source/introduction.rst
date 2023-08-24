The Squirrel Prover is a proof assistant for cryptographic protocols.
It is based on a higher-order version of the Bana-Comon logic,
and provides guarantees in the computational model.
You may find more information on the
`Squirrel homepage <https://squirrel-prover.github.io/>`_
or get the source code of the tool from
`our repository <https://github.com/squirrel-prover/squirrel-prover/>`_.

.. note::
   The Squirrel project started in 2020, and
   the tool is still under active development.
   This documentation is even more recent, and under construction.
   Please bear with us and do not hesitate to contact us to report
   problems or ask for clarifications.

You are reading the user's documentation. This documentation is not
meant as a first introduction to Squirrel; a linear read for people
unfamiliar with all the high level concepts will be difficult. For a
first introduction, we recommend to start with the :ref:`tutorial
<tutorial>`.

In this documention, the languages used in Squirrel are introduced in
distinct sections:

.. TODO there must be a better way to cite (sub)sections of doc

- protocols are modelled as :ref:`processes <section-processes>`
  from which :term:`systems <system>` are extracted;
- properties of these systems are expressed using the local and global
  formulas of our :ref:`logic <section-logic>`;
- finally, proving these properties is done using a
  :ref:`tactic language <section-proofs>`.

A Squirrel file consists of a list of directives that impact
the prover state:

- :ref:`declarations <section-declarations>`,
  which introduce new function symbols, cryptographic
  assumptions, processes, systems, and goals (i.e. lemmas or theorems);
- :ref:`commands <section-commands>`,
  which are used to enter or exit the proof mode,
  query the current state of the prover
  (e.g. find lemmas about a given function symbol) or
  tweak the tool's behaviour (e.g. control timeouts);
- finally, when in proof mode, :ref:`tactics <section-proofs>`
  are used to reduce the first subgoal to new subgoals.

For a more theoretical perspective on Squirrel,
you may read some of the associated publications:
:cite:`bdjkm21sp` for the original paper,
:cite:`bdkm22csf` for the extension to stateful protocols,
:cite:`cfj22sp` for the extension to post-quantum attackers and
:cite:`bkl23hal` for the up to date presentation of the logic.

.. note::
  This documentation heavily borrows from the infrastructure of the
  `Coq reference manual <https://coq.inria.fr/distrib/current/refman/>`_
  which is itself built on top of the
  `Sphinx framework <https://www.sphinx-doc.org/en/master/>`_.
  We thank the Coq and Sphinx developpers for their precious work!
