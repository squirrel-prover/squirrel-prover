========
Language
========

Here we define the syntax and informal semantics of our terms and formulas.
We also document the various declarations available in the prover,
and commands.

TODO can't see subsections in toc and navbar

Syntax
======

Types
-----

Squirrel comes with several builtin base types:

* :gdef:`message` represents bitstrings;
* :gdef:`bool` represents a single bit;
* :gdef:`timestamp` represents the points in a finite execution trace;
* :gdef:`index` represent an arbitrary finite set used to index
  unbounded collections of objects.

.. note:: When we say that a type is finite, it is still unbounded:
  the semantics for the type can be any finite set.

The user may define other base types TODO

TODO what's the proper way to reference terms?
should we do the same for technical terms such as message
and bool?

Arbitrary :gdef:`types <type>` are simple types, derived from base types
and type variables using the arrow and tupling type constructors.

  type ::= alpha | base-type | type -> type | (type * ... * type)

TODO better rendering for syntax

.. note:: The most common function symbols have
  types of the form ``(b1*...*bn)->b'`` where the ``b1``, ...,
  ``bn`` and ``b'`` are base types.

  For example, a hash function will have type
  ``(message*message)->message``: it takes a message to be hashed,
  a key, and the returned hash is also a message.

  .. squirreltop:: all

     hash h.
     (* declare something *)
     print h.

  TODO cannot write comments in squirrel top; do not show empty output?

Terms
-----

:gdef:`Terms <term>` are syntactic expressions that denote probabilistic
values.
For instance, a term of type :term:`message` represents a probabilistic value
which ranges over messages, and a term of type :term:`bool`
is a probabilistic boolean value.

Term syntax, lambda calculus TODO

.. note::
  Unlike in the original BC logic and the meta-logic that was used at first
  in Squirrel, our terms are not necessarily computable in polynomial time
  by probabilistic Turing machines.
  An example of a non-PTIME term is ``forall (x:message), x = f(x)``
  which tests whether ``f`` is idempotent, something that is not
  necessarily computable even when ``f`` is PTIME.

  TODO citations, colors for terms

Formulas
--------

Squirrel features two kinds of formulas: local and global ones.

:gdef:`Local formulas <local formula>`
are simply `terms`_ of type `bool`_. They can in particular be constructed
using common syntax, given below

   phi ::= (phi && phi) | (phi || phi) | (phi => phi) | not phi
         | forall <binders>, phi | exists <binders>, phi

Declarations
============

Symbols
-------

Systems
-------

Goals
-----

Commands
========

Print, help, search, etc.
