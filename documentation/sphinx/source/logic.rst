.. _section-logic:

======
Logic
======

Here we define the syntax and informal semantics of our logic,
and the various declarations available in the prover to introduce
new function symbols, cryptographic primitives, types, etc.

Systems will be documented elsewhere as they are not tied to the
logic.

Types
======

Base types
-----------

A base type can generally be thought of as a set of bitstrings,
though this is a simplified view as we shall see below.

.. prodn::
  base_type ::= bool | message | timestamp | index | @identifier

Squirrel comes with several builtin base types:

* :gdef:`message` represents bitstrings;
* :gdef:`bool` represents a single bit;
* :gdef:`timestamp` represents the points in a finite execution trace;
* :gdef:`index` represent an arbitrary finite set used to index
  unbounded collections of objects.

.. note:: A finite type is still unbounded:
  the semantics for the type can be any finite set.

Additional :gdef:`custom types` may be declared by the user
using the following declaration:

.. decl:: type @identifier {? [ {+, @type_tag } ] }

  Declare a new type called :token:`identifier`.
  The values of that type are assumed to be convertible to bitstrings,
  hence the type is a subtype of :g:`message`. Tags can optionally
  be passed to indicate assumptions on the new type.

  .. prodn::
    type_tag ::= large | well_founded | finite | fixed | name_fixed_length

  The meaning of tags is as follows:

  * a type is :gdef:`well-founded` when :g:`<` is well-founded
    on that type, for any :math:`\eta`;
  * a type is :gdef:`finite` if
    it has a finite cardinal for each :math:`\eta`;
  * a type is :gdef:`fixed` if it is the same for all :math:`\eta`;
  * a type is :gdef:`large` when it supports drawing any number of
    values, denoted by :term:`names <name>`, in such a way that two
    distinct names have a negligible chance of being equal;
  * a type with :gdef:`name_fixed_length` means that all names sampled
    in that type (for a given :math:`\eta`) have the same length;

General types
--------------

General types are derived from base types and type variables using the
arrow and tupling type constructors.  A type (or part of a type) can
be left unwritten using a type holes `_`, which must be then
inferred by Squirrel.

.. prodn::
  type ::= _ | @type_variable | @base_type | @type -> @type | (@type * ... * @type)

.. note:: The most common function symbols have
  types of the form ``(b1*...*bn)->b'`` where the ``b1``, ...,
  ``bn`` and ``b'`` are base types.

  For example, a hash function will have type
  ``(message*message)->message``: it takes a message to be hashed,
  a key, and the returned hash is also a message.

Binders and tags
================

.. prodn::
  variable ::= @identifier
  var_or_pat ::= _ | @variable

:token:`variable` are represented by string identifiers. 
A hole `_` can be used as name for a variable which is either unused
or whose name does not matter. 

Note that two occurrences of the same variable name are internally
bound to different variables (there is a hidden unique identifier).

.. prodn::
  tag ::= @identifier

Tags restrict a type in various ways.

TODO describe tags

.. prodn::
  binder ::= @var_or_pat | ({+, {+, @var_or_pat } : @type {? [{+ @tag}]} }) 
  binders ::= {* @binder }

Binders with tags are not supported everywhere.

TODO describe binders

Terms
======

:gdef:`Terms <term>` are syntactic expressions that denote probabilistic
values.
For instance, a term of type :term:`message` represents a probabilistic value
which ranges over messages, and a term of type :term:`bool`
is a probabilistic boolean value.

.. prodn::
  term ::= (@sterm) 
       | @term @ @term 
       | @term @term 
       | @term @infix_op @term 
       | @term # @natural
       | fun @binders => @term
       | @quantif @binders, @term
       | if @term then @term else @term 
       | find @binders such that @term in @term {? else @term }
  sterm ::= _
        | @identifier
        | diff(@term, @term)
        | ( {+, @term} )
  quantif ::= forall | exists

Term syntax, lambda calculus TODO

TODO :gdef:`names <name>`

.. note::
  Unlike in the original BC logic and the meta-logic that was used at first
  in Squirrel, our terms are not necessarily computable in polynomial time
  by probabilistic Turing machines.
  An example of a non-PTIME term is ``forall (x:message), x = f(x)``
  which tests whether ``f`` is idempotent, something that is not
  necessarily computable even when ``f`` is PTIME.

  TODO citations

**TODO** introduce :gdef:`macro` and :gdef:`system`.

Formulas
=========

Squirrel features two kinds of formulas: local and global ones.

:gdef:`Local formulas <local formula>`
are `terms`_ of type `bool`_. They can in particular be constructed
using common syntax, given below:

.. prodn::
  formula ::= @formula && @formula | @formula || @formula | @formula => @formula | not @formula
    | @quantif @binders, @formula
    | happens({+, @terms}) | cond@@term | exec@@term
    | @term = @term | @term <= @term | @term < @term | @term >= @term | @term > @term

TODO generalized infix operators

:gdef:`Global formulas <global formula>`
are first order formulas, written as follows:

.. prodn::
  global_formula ::= [@formula] | equiv({*, @term})
    | @global_formula -> @global_formula
    | @global_formula /\ @global_formula | @global_formula \/ @global_formula
    | Forall @binders, @global_formula | Exists @binders, @global_formula

.. _section-declarations:

Declarations
=============

Symbols
--------

Function symbols are deterministic polynomial time.

Systems
--------

.. prodn::
  system_id ::= identifier | identifier / identifier
  system_expr ::= {| any | {+, @system_id} }

TODO expr and set expressions

Goals
------

.. prodn::
  goal ::= local_goal
  local_goal ::= {? local } goal {? @system_expr } {| @identifier | _ } @parameters : @formula
  global_goal ::= global goal {? @system_expr } {| @identifier | _ } @parameters : @global_formula

.. example:: Unnamed local goal

  :g:`goal [myProtocol/left] _ : cond@A2 => input@A1 = ok.`

.. example:: Global goal expressing observational equivalence

  :g:`global goal [myProtocol] obs_equiv (t:timestamp) : happens(t) => equiv(frame@t).`
