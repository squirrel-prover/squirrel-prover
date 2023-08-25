.. _section-logic:

======
Logic
======

We here define the syntax and informal semantics of our logic
independently from protocols and cryptographic construcs.

Types
======

Base types
-----------

A base type can generally be thought of as a set of bitstrings,
though this is a simplified view as we shall see below.

.. prodn::
  base_type ::= bool | message | timestamp | index | @identifier

Squirrel comes with several builtin base types:

* :gdef:`message` represents bitstrings.
* :gdef:`bool` represents a single bit.
* :gdef:`timestamp` represents the points in a finite execution trace. 
* :gdef:`index` represents an arbitrary finite set used to index
  unbounded collections of objects.

Additional :gdef:`custom types` may be declared by the user
using the following declaration:

.. decl:: type @identifier {? [ {+, @type_tag } ] }

  Declare a new type called :token:`identifier`.
  The values of that type are assumed to be convertible to bitstrings,
  hence the type is a subtype of :g:`message`. Tags can optionally
  be passed to indicate assumptions on the new type, which intuitively puts restriction on the underlying set of bitstrings.

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

The underlying parameter :math:`\eta` corresponds to the security parameter used in security proofs, and names are then used to model the sampling of nonces of length :math:`\eta`.

.. note:: A finite type is still unbounded:
          the semantics for the type can be any finite set.

    
Type variables
--------------

Squirrel supports parametric polymorphism à la `Hindley–Milner <https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system>`_. 
Type variables can be represented by any identifier preceded by a
single apostrophe, e.g. :n:`'x`.

.. prodn::
  type_variable ::= '@identifier

General types
--------------

General types are derived from base types and type variables using the
arrow and tupling type constructors.  A type (or part of a type) can
be left unwritten using a type holes :g:`_`, which must then be
inferred by Squirrel.

.. prodn::
  type ::= _ | @type_variable | @base_type | @type -> @type | (@type * ... * @type)

The most common function symbols have types of the form :g:`(b1 * ... * bn) -> b` where :g:`b1,...,bn` and :g:`b` are base types.

.. example:: Hash function
	     
   A hash function may have type :g:`(message * message) -> message`:
   it takes a message to be hashedand a key, and the returned hash is
   also a message. Given that any hash value often has a constant
   length, a specific type for the hash outputs could also be defined
   as a :g:`fixed` type.
  
Binders and tags
----------------

:token:`variable` are represented by string identifiers. 
A hole `_` can be used as name for a variable which is either unused
or whose name does not matter. 

.. prodn::
  variable ::= @identifier
  var_or_hole ::= @variable | _

:gdef:`Tags <tag>` restrict a possible variable instantiation in various ways.

.. prodn::
  tag ::= const | glob | adv
  
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
- :gdef:`adv` forces the variable to be computable by a PTTM with
  access to a dedicated randomness tape. This tag is used to define
  adversarial functions, that can be seen as probabilist polynomial
  time attackers.

.. note::
   Squirrel includes a builtin function symbol :g:`att :
   message -> message [adv]` that can be used to refer to an
   adversary.
 
Squirrel uses the following syntax for binders:

.. prodn::
  binder ::= @var_or_hole | ({+, {+, @var_or_hole } : @type {? [{+ @tag}]} }) 
  binders ::= {* @binder }

A binder :g:`x` without any attached (using directly a
:n:`@var_or_hole`) is equivalent to using a type hole :g:`(x:_)`.
The type hole will have to be inferred by unification.

.. note:: Tags in binders do not always have a meaning, e.g., in the
          function declared with an :term:`abstraction` as follows
          :g:`fun(x:int[const])=>f`, Squirrel will ignore the tags in
          such cases.

.. note:: Binding twice the same variable name yields two distinct
          variables (there is a hidden unique identifier).

Terms
=====

:gdef:`Terms <term>` are syntactic expressions that denote
probabilistic values (families of probabilistic values indexed
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
  :term:`abstract function<abstract_fun>`.
- a :term:`diff-term` representing several probabilistic values which depend
  on the system;
- a tuple :n:`(@term__1,...,@term__n)`.

.. todo::
   Charlie: Can an identifier be other things?

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

:gdef:`Abstractions <abstraction>` are of the form :n:`fun @binders => @term` where
:n:`@term` can use the variables bound by :n:`@binders`.
E.g. :n:`fun(x:@type)=>@term__body` is the function that maps a value
:n:`x` of type :n:`type` to :n:`@term__body`.

Universal or existential *quantification* are of the form 
:n:`@quantif @binders, @term` , e.g. :n:`forall @binders,@term__pred` where
:n:`@term__pred` must be of type :g:`bool`.

Multiple binders in an abstraction or quantifier construct represent
multiple nested constructs, e.g. :n:`fun x y=>@term` is a short form
for :n:`fun x=>(fun y=>@term)`.

A :n:`find` performs a look-up through all values of a type, filtered
according to some predicate, and returining some computation. E.g. if
:n:`@term__b` is of type :g:`bool` and :n:`@term__i` and :n:`@term__e`
have the same type, then 
:n:`find(x:@type)such that @term__b in @term__i else @term__e` 
looks for some :n:`x` of type :n:`type` such that
:n:`@term__b`: if such a value exists, it returns :n:`@term__b`,
otherwise it returns :n:`@term__e` (terms :n:`@term__b` and
:n:`@term__i` can use the variable :n:`x`, while :n:`@term__b`
cannot). If no :n:`else` branch term is provided, :n:`@term__e`
defaults to :g:`zero` (the zero bit-string).

.. note:: :term:`Tags <tag>` are not supported in term binders. They are
          accepted by the parser, but ignored by Squirrel.



Diff-terms
-----------

:gdef:`Diff-terms <diff-term>` of the form :n:`diff(@term__1,@term__2)` represents
two terms at once. This is a convinient way to define two similar
terms except for a small part. Later on, they will be used to
define easily two protocols that only slightly differ. The logic
in the tool allows to reason on diff-terms, proving for instance
that the two representations are equivalent.

.. prodn:: 
   diff_term ::= diff(@term, @term)


Formulas
========

Squirrel features two kinds of formulas: local and global ones.

Local formulas
--------------

:gdef:`Local formulas <local formula>` are :term:`terms <term>` of
type :g:`bool`. They correspond to the embedding of a lower-level logic inside of our terms. They can in particular be constructed using common
syntax and construction specific to Squirrel described below:

.. prodn::
  term += @term && @term | @term %|%| @term | @term => @term | not @term
    | happens({+, @term}) 

Boolean connectives for *local* formulas are :n:`&&, ||, =>, not`,
where :n:`&&, ||, =>` are used with a right infix notation, and
:n:`not` in prenex form. Bear in mind that those connectives are in
fact classical function symbols of the terms.

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

The classical construction of the first-order logic mostly behave as expected.

.. note:: Compared to the paper presentations of the logic, where
   diff-terms don't exist, the universal quantifiers can in Squirrel
   be instantiated by diff-terms. The :g:`glob` tag allows to restric
   quantifications over non diff-terms.


The :n:`[@term]` predicates holds if :n:`@term`  evaluates to true with overwhelming probability.

.. _section-judgements:

