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

Squirrel comes with several built-in base types:

* :gdef:`message` represents bitstrings.
* :gdef:`bool` represents a single bit.
* :gdef:`timestamp` represents the points in a finite execution trace. 
* :gdef:`index` represents an arbitrary finite set used to index
  unbounded collections of objects.

Additional :gdef:`custom types` may be declared by the user
using the following declaration:

.. decl:: type @identifier {? [ {+, @type_tag } ] }

  Declare a new base type called :n:`@identifier`.
  The values of that type are assumed to be encodable as bitstrings.
  :gdef:`Type tags<type tag>` can optionally be passed to restrict the new 
  type possible instantiations.

  .. prodn::
    type_tag ::= large | well_founded | finite | fixed | name_fixed_length

  Tags have the following semantics:

  * a type is :gdef:`well-founded` when the :term:`built-in` function symbol :g:`<` is well-founded
    on that type, for any :math:`\eta`;
  * a type is :gdef:`finite` if
    it has a finite cardinal for each :math:`\eta`;
  * a type is :gdef:`fixed` if its interpretation does not depend on :math:`\eta`;
  * a type is :gdef:`large` when random samplings over that type
    (using :term:`names <name>`) are such that two
    distinct names have a negligible probability of collision;
  * a type is :gdef:`name_fixed_length` if all :term:`names<name>`
    over that type sample values of the same length (for a given
    :math:`\eta`).

The parameter :math:`\eta` corresponds to the underlying security parameter used in security proofs.

.. note:: A finite type is still unbounded:
          the semantics for the type can be any finite set.


.. _section-polymorphism:

Type variables and polymorphism
-------------------------------

Squirrel supports :gdef:`parametric type polymorphism<polymorphism>` à la `Hindley–Milner <https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system>`_ in most places (in :term:`operators<operator>`, :term:`goals<goal>`, ...).
Type variables must be an identifier preceded by a
single apostrophe, e.g. :n:`'x`.

.. prodn::
  type_variable ::= '@identifier
  tvar_params ::=  {* @type_variable }

When parametrizing a declaration, type variables are enclosed in brackets, e.g. :g:`['a 'b 'c]`.


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
	     
   A hash function may have type :g:`(message * key_ty) -> hash_ty`:
   it takes as input the value to be hashed (of type :g:`message`) and a
   key (of type :g:`key_ty`), and returns a digest of type :g:`hash_ty`.

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
  
Currently, only a few different tags are supported. A tagged bound
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
   Squirrel includes a built-in function symbol :g:`att :
   message -> message [adv]` that can be used to refer to an
   adversary.
 
Squirrel uses the following syntax for binders:

.. prodn::
  binder ::= @var_or_hole | ({+, {+, @var_or_hole } : @type {? [{+ @tag}]} }) 
  binders ::= {* @binder }

A bound variable :g:`x` without any attached type (i.e. using directly a
:n:`@var_or_hole`) amounts to use a type hole :g:`(x:_)`,
which will have to be be inferred by Squirrel.

.. note:: Not all binders support tags, e.g. it would be meaningless
          to declare a function :term:`abstraction` with a :g:`const`
          tag, as in :g:`fun(x:int[const])=>t`.

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
       | @name_id {? @term}
       | @term # @natural
       | @macro_application
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
- a name term application :n:`@name_id {? @term__i}`, see :term:`names<name>`;
- the projection :n:`@term # i` of :n:`@term` over its :n:`i`-th component
  (:n:`@term` must be a tuple with sufficiently many elements);
- a macro term, see :term:`macro`;
- an conditional :n:`if @term__b then @term__0 else @term__1` where
  :n:`@term__b` must be of type :g:`bool`, and :n:`@term__0` and
  :n:`@term__1` must have the same type;
- a term with binders, see :token:`term_with_binders`;
- an identifier :n:`x`, which must be bound by the context, and can be
  a :term:`logical variable <logical_var>`, an :term:`operator`, or an
  :term:`abstract function<abstract_fun>`.
- a :term:`diff-term` representing several probabilistic values which depend
  on the system;
- a tuple :n:`(@term__1,...,@term__n)`.

.. todo::
   Charlie: Can an identifier be other things?

   Adrien: I think this is it.

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
according to some predicate, and returning some computation. E.g. if
:n:`@term__b` is of type :g:`bool` and :n:`@term__i` and :n:`@term__e`
have the same type, then 
:n:`find(x:@type)such that @term__b in @term__i else @term__e` 
looks for some :n:`x` of type :n:`type` such that
:n:`@term__b`: if such a value exists, it returns :n:`@term__b`,
otherwise it returns :n:`@term__e` (terms :n:`@term__b` and
:n:`@term__i` can use the variable :n:`x`, while :n:`@term__b`
cannot). If no :n:`else` branch term is provided, :n:`@term__e`
defaults to :g:`zero` (the zero bit-string).


Multi-terms
===========

A k :gdef:`multi-term` is a single syntactic object used to represents a
k-tuple of terms.
Squirrel syntax allows to factorize common behavior between the
components of a multi-terms by writting a *single syntactic object*
--- the multi-term --- which can have sub-terms representing diverging
behavior between its components using:

* the :n:`diff` construct, see :term:`diff-terms<diff-term>`;
* and :term:`macro terms<macro>` when reasoning over multiple
  :term:`systems<system>` simultaneously.

There is no syntactic separation between terms and multi-terms: any
Squirrel term can be a multi-terms (though syntactic checks are
performed in some places when it is necessary that the user provides a
single term to Squirrel).

Squirrel heavily uses multi-terms. Most notably, the equivalence
between two terms :n:`t__1` and :n:`t__2` can be denoted by an
:term:`equivalence atom` :n:`equiv(@term__bi)`,
where :n:`@term__bi` is any bi-term (i.e. a 2 multi-term) such that
its left (resp. right) component is :n:`t__1` (resp. :n:`t__1`).
   
..  
  :term:`systems<system>` 

  Squirrel syntax for bi-terms allow to factorize
  common behavior by


Diff-terms
-----------

.. prodn:: 
   diff_term ::= diff(@term, @term)

:n:`diff(@term__1,@term__2)` is a :gdef:`diff-term <diff-term>`
representing a diverging behavior between the *left* component
:n:`@term__1` and the *right* component :n:`@term__2`.
Currently, diff-terms can only have two components, hence can only be
used in bi-terms. 


Macros
------

:gdef:`Macros <macro>` are a special built-in *probabilistic*
functions defined by recurence over the execution trace (i.e. the 
:g:`timestamp` type). 
Applied macros can occur in terms as follows:

.. prodn::
   macro_id ::= @identifier
   macro_application ::= @macro_id {* @term} @ @term

The timestamp argument :n:`ts` of a macro :n:`@macro_id` is passed using a special syntax :n:`@macro_id @ ts`.

The term :n:`@macro_id @term__1 ... @term_n @ @term__t` represents the
application of macro symbol :n:`@macro_id` which arguments
:n:`@term__1 ... @term_n` at a time-point :n:`@term__t` (of type
:g:`timestamp`).

The semantics of a macro symbol :n:`@macro_id` depends on the systems
it is being interpreted in:

* its semantics over a :term:`single system`, depends on the system
  definition, see the :ref:`system-defined macros section
  <section-system-macros>`.

* over a :term:`multi-system` :n:`P__1,...,P__n`, it
  represents a :n:`n` mutli-term, where the :n:`i`-th component corresponds to
  the interpretation of the macro over the single system :n:`P__i`.

   
Formulas
========

Squirrel features two kinds of formulas: :term:`local formulas<local
formula>` and :term:`global formulas<global formula>`.

Local formulas
--------------

:gdef:`Local formulas <local formula>` are :term:`terms <term>` of
type :g:`bool`. They correspond to the embedding of a lower-level
logic inside using terms.  They can in particular be constructed using
the following (standard and Squirrel-specific) logical constructs:

.. prodn::
  term += @term && @term | @term %|%| @term | @term => @term | not @term
    | happens({+, @term}) 

Boolean connectives for *local* formulas are :n:`&&, ||, =>, not`,
where :n:`&&, ||, =>` are used with a right infix notation, and
:n:`not` in prenex form. Bear in mind that those connectives are in
fact classical function symbols of the terms.

.. todo::
   Adrien: "Bear in mind ... of the terms" => I did not understand
   
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

Global boolean connectives :n:`->, /\, \/` are used in infix
notation, and have a standard semantics.

An :gdef:`reachability atom` :n:`[@term]` holds if :n:`@term` evaluates to true with overwhelming probability.

An :gdef:`equivalence atom` :n:`@equiv(@term__1,...,@term__n)` holds if
:n:`@term__1,...,@term__n` are diff-terms which any PPTM adversary has
at most a negligible probability of distinguishing

.. note:: Compared to the paper presentations of the logic, where
   diff-terms don't exist, universal quantifiers can in Squirrel
   be instantiated by diff-terms. The :g:`glob` variable tag allows to restric
   quantifications over non diff-terms.

.. todo::
   Adrien: I feel like this note is slightly out-of-place here. Maybe in the section of diff-terms?
   
.. _section-judgements:

