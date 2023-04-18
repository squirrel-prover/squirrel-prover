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

Type variables
--------------

Squirrel supports parametric polymorphism à la Hindley–Milner. 
Type variables can be represented by any identifier preceded by a
single apostrophe, e.g. :n:`'x`.

.. prodn::
  type_variable ::= '@identifier

General types
--------------

General types are derived from base types and type variables using the
arrow and tupling type constructors.  A type (or part of a type) can
be left unwritten using a type holes :g:`_`, which must be then
inferred by Squirrel.

.. prodn::
  type ::= _ | @type_variable | @base_type | @type -> @type | (@type * ... * @type)

.. note:: The most common function symbols have types of the form
  :g:`(b1 * ... * bn) -> b` where :g:`b1,...,bn` and :g:`b` are base
  types.

  For example, a hash function may have type
  :g:`(message * message) -> message`: it takes a message to be hashed,
  a key, and the returned hash is also a message.

Binders and tags
----------------

:token:`variable` are represented by string identifiers. 
A hole `_` can be used as name for a variable which is either unused
or whose name does not matter. 

.. prodn::
  variable ::= @identifier
  var_or_hole ::= @variable | _

:gdef:`Tags <tag>` restrict a possible variable instantiation various ways.

.. prodn::
  tag ::= const | glob

Currently, only two different tags are supported. A tagged bound
variable :g:`(x : t[tag])` restricts :g:`x` instantiations according
to :g:`tag`:

- :gdef:`const` requires that :g:`x` is a constant random variable,
  which does not depend on the random tape nor the security parameter
  :math:`\eta`.
- :gdef:`glob` forces :g:`x` to be a *single* random variable --- said
  otherwise, :g:`x` must represent a *system-independent* random
  variable ; for example, this excludes any :term:`diff-term`
  (e.g. :g:`diff(s,t)`), or any term with system-specific macros
  (e.g. :g:`output@tau`).

Squirrel uses the following syntax for binders:

.. prodn::
  binder ::= @var_or_hole | ({+, {+, @var_or_hole } : @type {? [{+ @tag}]} }) 
  binders ::= {* @binder }

A binder :g:`x` without any attached (using directly a
:n:`@var_or_hole`) is equivalent to using a type hole :g:`(x:_)`.
The type hole will have to be inferred by unification.

.. note:: Tags in binders do not always have a meaning, e.g. in the
          function :g:`fun(x:int[const])=>f`. Squirrel will
          ignore the tags in such cases.

.. note:: Binding twice the same variable name yields two distinct
          variables (there is a hidden unique identifier).

Terms
=====

:gdef:`Terms <term>` are syntactic expressions that denote
probabilistic values (actualy families of probabilistic values indexed
by the security parameter :math:`\eta`, though this can often be
ignored).
For instance, a term of type :g:`message` represents a
probabilistic value which ranges over messages, and a term of type
:g:`bool` is a probabilistic boolean value.

.. prodn::
  term ::= @term {+ @term } 
       | @term @infix_op @term 
       | @term # @natural
       | @term @ @term 
       | if @term then @term else @term 
       | @term_with_binders
       | @sterm
  sterm ::= _
        | @identifier
        | @diff_term
        | ( {+, @term} )

A term can be

- an application :n:`@term__1 @term__2` ; application is
  left-associative, and the term :n:`@term__1 @term__2 ... @term__n`
  corresponds to :n:`(...(@term__1 @term__2) ... @term__n)`;
- the application of an infix operator :n:`@term__1 @infix_op @term__2`, 
  which corresponds :n:`(@infix_op) @term__1 @term__2`;
- the projection :n:`@term # i` of :n:`@term` over its :n:`i`-th component
  (:n:`@term` must be a tuple with sufficiently many elements);
- the application :n:`@term__m @ @term__t` of a macro term
  :n:`@term__m` at a time-point :n:`@term__t` (of type :g:`timestamp`); this is only 
  possible if :n:`@term__m` is a :term:`macro`;
- an conditional :n:`if @term__b then @term__0 else @term__1` where
  :n:`@term__b` must be of type :g:`bool`, and :n:`@term__0` and
  :n:`@term__1` must have the same type;
- a term with binders, see :token:`term_with_binders`;
- an identifier :n:`x`, which must be bound by the context, and can be
  a :term:`logical variable <logical_var>`, an :term:`operator`, an
  :term:`abstract function<abstract_fun>`, or TODO (more?);
- a :term:`diff-term` representing several probabilistic values which depend
  on the system;
- a tuple :n:`(@term__1,...,@term__n)`.


.. note:: Many tactics use :token:`sterm` instead of :token:`term`,
           which creates less ambiguities in the parser.  Note that
           enclosing a :token:`term` in parentheses yields a
           :token:`sterm`.

Terms with binders
------------------

.. prodn:: 
   term_with_binders ::= fun @binders => @term
                    | @quantif @binders, @term
                    | find @binders such that @term in @term {? else @term }
  quantif ::= forall | exists

A term with binders can be:

- an abstraction, e.g. :n:`fun(x:@type)=>@term__body` is the
  function that maps a value :n:`x` of type :n:`type` to
  :n:`@term__body`;
- a universal or existential quantification, e.g. 
  :n:`forall @binders,@term__pred` 
  where :n:`@term__pred` must be of type :g:`bool`;
- a try-find construct, e.g. if :n:`@term__b` is of type
  :g:`bool` and :n:`@term__i` and :n:`@term__e` have the same
  type, then
  :n:`find(x:@type)such that @term__b in @term__i else @term__e`
  search a :n:`x` of type :n:`type` such that :n:`@term__b`: if such a value exists, 
  it returns :n:`@term__b`, otherwise it returns :n:`@term__e` (terms
  :n:`@term__b` and :n:`@term__i` can use the variable :n:`x`, while
  :n:`@term__b` cannot).

.. note:: :term:`Tags <tag>` are not supported in term binders. They are
          accepted by the parser, but ignored by Squirrel.



Diff-terms
----------

TODO :gdef:`diff-terms <diff-term>` of the form :n:`diff(@term__1,@term__2)` represents ...

.. prodn:: 
   diff_term ::= diff(@term, @term)

Names
-----

TODO :gdef:`names <name>`

.. note::
  Unlike in the original BC logic and the meta-logic that was used at first
  in Squirrel, our terms are not necessarily computable in polynomial time
  by probabilistic Turing machines.
  An example of a non-PTIME term is ``forall (x:message), x = f(x)``
  which tests whether ``f`` is idempotent, something that is not
  necessarily computable even when ``f`` is PTIME.

  TODO citations

Macros
------

TODO :gdef:`macros <macro>`

Formulas
========

Squirrel features two kinds of formulas: local and global ones.

Local formulas
--------------

:gdef:`Local formulas <local formula>` are :term:`terms <term>` of
type :g:`bool`. They can in particular be constructed using common
syntax and construction specific to Squirrel describdee below:

.. prodn::
  term += @term && @term | @term %|%| @term | @term => @term | not @term
    | happens({+, @term}) 

Boolean connectives for *local* formulas are :n:`&&, ||, =>, not`,
where :n:`&&, ||, =>` are used with a right infix notation, and
:n:`not` in prenex form.

The :gdef:`happens` predicate defines the time-points that have been
scheduled in the execution, e.g. :n:`happens(@term)` (where :n:`@term`
is of type :g:`timestamp`) state that :n:`@term` has been scheduled.
:n:`happens(@term__1,...,@term__n)` is syntactic sugar (provided by
the parser) for :n:`happens(@term__1)&&...&&@happens(term__n)`.

..
  I removed this production, which did not make sens with the current
  style of introducing term syntax.
  .. prodn::
    formula ::= @formula && @formula | @formula || @formula | @formula => @formula | not @formula
      | @quantif @binders, @formula
      | happens({+, @term}) | cond@@term | exec@@term
      | @term = @term | @term <= @term | @term < @term | @term >= @term | @term > @term

Global formulas
---------------

:gdef:`Global formulas <global formula>`
are first order formulas, written as follows:

.. prodn::
  global_formula ::= [@term] | equiv({*, @term})
    | @global_formula -> @global_formula
    | @global_formula /\ @global_formula | @global_formula \/ @global_formula
    | Forall @binders, @global_formula | Exists @binders, @global_formula

TODO description

.. _section-declarations:

Declarations
=============

Abstract symbols
----------------

:gdef:`Abstract functions<abstract_fun>` TODO

Function symbols are deterministic polynomial time.

Operators
---------

:gdef:`Operators <operator>`

Systems
-------

:gdef:`systems <system>` TODO

.. prodn::
  system_id ::= identifier | identifier / identifier
  system_expr ::= {| any | {+, @system_id} }

TODO expr and set expressions

Goals
-----

.. prodn::
  goal ::= local_goal
  local_goal ::= {? local } goal {? @system_expr } {| @identifier | _ } @parameters : @formula
  global_goal ::= global goal {? @system_expr } {| @identifier | _ } @parameters : @global_formula

.. example:: Unnamed local goal

  :g:`goal [myProtocol/left] _ : cond@A2 => input@A1 = ok.`

.. example:: Global goal expressing observational equivalence

  :g:`global goal [myProtocol] obs_equiv (t:timestamp) : happens(t) => equiv(frame@t).`

.. _section-judgements:

Judgements
==========

TODO

Logical variables
-----------------

:gdef:`Logical variable <logical_var>` TODO
