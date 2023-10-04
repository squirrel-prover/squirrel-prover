.. _section-logic:

======
Logic
======

We define here the syntax and informal semantics of our logic
independently from protocols and cryptographic constructs.

Types
======

Base types
-----------

A base type can generally be thought of as a set of bitstrings,
though this is a simplified view as we shall see below.

.. prodn::
  base_type ::= bool | message | timestamp | index | @ident

Squirrel comes with several built-in base types:

* :gdef:`message` represents bitstrings;
* :gdef:`bool` represents a single bit;
* :gdef:`timestamp` represents the points in a finite execution trace;
* :gdef:`index` represents an arbitrary finite set used to index
  unbounded collections of objects.

Additional :gdef:`custom types` may be declared by the user
using the following declaration:

.. decl:: type @ident {? [ {+, @type_tag } ] }

  Declare a new base type called :n:`@ident`.
  The values of that type are assumed to be encodable as bitstrings.
  :gdef:`Type tags<type tag>` can optionally be passed to impose
  assumptions on the type's implementation.

  .. prodn::
    type_tag ::= large | well_founded | finite | fixed | name_fixed_length

  Tags have the following semantics:

  * a type is :gdef:`well-founded` when the :term:`built-in` function
    symbol :g:`<` is well-founded on that type, for any :math:`\eta`;
  * a type is :gdef:`finite` if
    it has a finite cardinal for each :math:`\eta`;
  * a type is :gdef:`fixed` if its interpretation does not depend on :math:`\eta`;
  * a type is :gdef:`large` when random samplings over that type
    (declared using :decl:`name <name>`) are such that two
    distinct names have a negligible probability of collision
    w.r.t to :math:`\eta`;
  * a type is :gdef:`name_fixed_length` if all :decl:`names<name>`
    over that type sample values of the same length (for a given
    :math:`\eta`).

  Built-ins types come with the following type tags:
  
  * :n:`message` is :g:`fixed`, :g:`well_founded`, :g:`name_fixed_length`
    and :g:`large`;
  * :n:`bool`, :n:`timestamp` and :n:`index` are
    :g:`fixed`, :g:`finite` and :g:`well_founded`.

The parameter :math:`\eta` corresponds to the underlying security
parameter used in security proofs.

.. note:: A finite type is still unbounded:
          the semantics for the type can be any finite set.


.. _section-polymorphism:

Type variables and polymorphism
-------------------------------

Squirrel supports :gdef:`type polymorphism<polymorphism>` à la `Hindley–Milner <https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system>`_ in most places (:decl:`operators<op>`, :term:`lemmas<lemma>`, ...).
Type variables are identifiers preceded by a
single apostrophe, e.g. :g:`'x`.

.. prodn::
  type_variable ::= '@ident
  tvar_params ::=  {* @type_variable }

When parametrizing a declaration, type variables are enclosed in brackets, e.g. :g:`['a 'b 'c]`.


General types
--------------

General types are derived from base types and type variables using the
arrow and tupling type constructors.  A type (or part of a type) can
be left unspecified using a type hole :g:`_`, which must then be
inferred by Squirrel.

.. prodn::
  explicit_type ::= @type_variable | @base_type | @type -> @type | (@type * ... * @type)
  type ::= _ | @explicit_type

The most common function symbols have types of the form :g:`(b1 * ... * bn) -> b` where :g:`b1,...,bn` and :g:`b` are base types.

.. example:: Hash function
       
   A hash function may have type :g:`(message * key_ty) -> hash_ty`:
   it takes as input the value to be hashed (of type :g:`message`) and a
   key (of type :g:`key_ty`), and returns a digest of type :g:`hash_ty`.

Binders and tags
----------------

A :token:`variable` is just an identifier.
A hole `_` can be used as name for a variable which is either unused
or whose name does not matter. 

.. prodn::
  variable ::= @ident
  var_or_hole ::= @variable | _

:gdef:`Variable tags <tag>` restrict a variable's possible instantiations
in various ways.

.. prodn::
  tag ::= const | glob | adv
  
Currently, only a few different tags are supported. A tagged bound
variable :g:`(x : t[tag])` restricts :g:`x`'s instantiations according
to :g:`tag`:

- Tag :gdef:`const` requires that :g:`x` is a constant random variable,
  which does not depend on the random tape nor the security parameter
  :math:`\eta`.
- Tag :gdef:`glob` forces :g:`x` to be a *single* random variable --- said
  otherwise, :g:`x` must represent a *system-independent* random
  variable ; for example, this excludes any :term:`diff-term`
  (e.g. :g:`diff(s,t)`), or any term with system-specific macros
  (e.g. :g:`output@tau`).
- Tag :gdef:`adv` forces :g:`x` to be computable by a probabilistic
  polynomial Turing Machine (PPTM) with access to a dedicated
  randomness tape. Such machines run in polynomial time w.r.t. to the
  security parameter and their input length. This tag is used to
  define adversarial functions, that can be seen as probabilistic
  polynomial time attackers.


Abstract function declarations cannot rely on tags, but we can declare
free variables of axioms using tags, as well as globally quantify
using tags.

.. example:: No guessing of large names

   If we assume that :g:`n` is a name over type :g:`message`, as
   :g:`message` is :g:`large`, it is a random value long enough
   w.r.t. to :math:`\eta` so that it can at best be guessed with
   negligible probability. A formula modeling that any function symbol
   computable by a PPTM cannot return the value of :g:`n` is expressed
   as :g:`Forall att : message -> message [adv], [att(0)=n]`. This is
   in fact a valid global axiom of the logic. We can also express the axiom
   by using the tag over the free variable of a local axiom, yielding
   :g:`axiom [any] test (att : message -> message [adv]) : att(r)=n`.
 
Squirrel uses the following syntax for binders:

.. prodn::  
  binder ::= @var_or_hole | ({+, {+, @var_or_hole } : @type {? [{+ @tag}]} }) 
  binders ::= {* @binder }

.. note::
  Tags actually correspond to predicates in the logic: for instance,
  :g:`forall (x:ty[const]), phi` should be understood as
  :g:`forall (x:ty), const(x) => phi` in the theory.
  Predicates such as :g:`const(_)` are however not directly accessible in
  the tool.

.. note:: Not all binders support tags, e.g. it would be meaningless
          to declare a function :term:`abstraction` with a :g:`const`
          tag, as in :g:`fun(x:int[const])=>t`.

A binding declaration :g:`x` without any attached type (i.e. using directly a
:n:`@var_or_hole`) amounts to using a type hole :g:`(x:_)`,
which will have to be be inferred by Squirrel.

.. example:: Type inference for bound variables

   In the formula :g:`forall (z:message), exists x y, z =x && x=y`,
   which is a valid **Squirrel** formula, the existential
   quantification uses the binder :g:`x y`, which is in fact
   equivalent to :g:`x:_ y:_` or :g:`(x,y:_)`. Here, **Squirrel**
   automatically infer the type of the variables from the equalities.

Terms
=====

:gdef:`Terms <term>` are syntactic expressions that denote
probabilistic values (or, more precisely,
families of probabilistic values indexed by the security parameter
:math:`\eta`, though this can often be ignored).
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
        | @ident
        | @diff_term
        | ( {+, @term} )

A term can be

- an application :n:`@term__1 @term__2` ; application is
  left-associative, and the term :n:`@term__1 @term__2 ... @term__n`
  corresponds to :n:`(...(@term__1 @term__2) ... @term__n)`;
- the application of an infix operator :n:`@term__1 @infix_op @term__2`, 
  which corresponds to :n:`(@infix_op) @term__1 @term__2`;
- a name term application :n:`@name_id {? @term__i}`, see
  :decl:`names<name>` (compared to the previous term application, here
  we must pass as many indices as the arity of the name, that is, the
  name must be fully instantiated);
- the projection :n:`@term # i` of :n:`@term` over its :n:`i`-th component
  (:n:`@term` must be a tuple with sufficiently many elements);
- a macro term, see :term:`macro`;
- a conditional :n:`if @term__b then @term__0 else @term__1` where
  :n:`@term__b` must be of type :g:`bool`, and :n:`@term__0` and
  :n:`@term__1` must have the same type (for a conditional over messages,
  the :n:`else` branch can be omitted, which stands for :n:`else zero`);
- a term with binders, see :token:`term_with_binders`;
- an identifier, which must be bound by the context (it can for instance refer to
  a :term:`logical variable <logical_var>`, an :decl:`operator<op>` or an
  :decl:`abstract function<abstract>` symbol);
- a :term:`diff-term` representing several probabilistic values which depend
  on the system;
- a tuple :n:`(@term__1,...,@term__n)`.

Many tactics use :token:`sterm` instead of :token:`term`,
which creates less ambiguities in the parser.  Note that
enclosing a :token:`term` in parentheses yields a
:token:`sterm`.

.. note::
   Since :cite:`bkl23hal`, terms no longer necessarily represent
   (PTIME) computable values.
   An example of a non PTIME-computable term is
   :g:`forall (x:message), x = f(x)`
   which tests whether :g:`f` is idempotent, something that is not
   necessarily computable even when :g:`f` is.

Terms with binders
------------------

.. prodn:: 
   term_with_binders ::= fun @binders => @term
                    | @quantif @binders, @term
                    | find @binders such that @term in @term {? else @term }
  quantif ::= forall | exists

:gdef:`Abstractions <abstraction>` are of the form :n:`fun @binders => @term` where
:n:`@term` can use the variables bound by :n:`@binders`.
For example,
:n:`fun (x:@type) => @term__body` is the function that maps a value
:n:`x` of type :n:`type` to :n:`@term__body`.

Universal or existential *quantifications* are of the form 
:n:`@quantif @binders, @term`
where :n:`@term` must be of type :g:`bool`.
For example, one can write :g:`exists (x:message), fst(x) = zero`.

Multiple binders in an abstraction or quantifier construct represent
multiple nested constructs, e.g. :n:`fun x y => @term` stands for
:n:`fun x => (fun y => @term)`.

A :n:`find` performs a look-up through all values of a type, filtered
according to some predicate, and returning some computation. For instance, if
:n:`@term__b` is of type :g:`bool` and :n:`@term__i` and :n:`@term__e`
have the same type, then 
:n:`find (x:@type) such that @term__b in @term__i else @term__e` 
looks for some :n:`x` of type :n:`type` such that
:n:`@term__b`: if such a value exists, it returns :n:`@term__b`,
otherwise it returns :n:`@term__e` (terms :n:`@term__b` and
:n:`@term__i` can use the variable :n:`x`, while :n:`@term__b`
cannot). If no :n:`else` branch term is provided, :n:`@term__e`
defaults to :g:`zero` (the zero bit-string).


Multi-terms
===========

In several circumstances, we have to manipulate several variants
of a term, which only differ in a few places. This happens when proving
equivalences, which are typically between minor variations of the same
term (e.g., equivalence between
an output :g:`enc(m,k)` and :g:`enc(zeroes(m),k)`). This also happens
when proving the same property for different systems: e.g., an authentication 
property might initially be identical for all systems, talking generically of
a message :g:`output@tau`, but unfolding this macro will reveal a different 
meaning for each system.

In order to factorize common parts of such collections of alternatives,
and factorize reasoning over them, Squirrel makes use of
:gdef:`multi-terms<multi-term>`.
A k-multi-term is a single syntactic object used to represent
k alternative terms. The common part of the terms is simply written
as a term, and the distinct parts are expressed using the
the :n:`diff` construct, see :term:`diff-terms<diff-term>`.
The i-th :gdef:`projection` of a multi-term :g:`t` is obtained from :g:`t`
by replacing any subterm of the form :g:`diff(t_1,..,t_n)`
by :g:`t_i`.

A :gdef:`bi-term` is a 2-multi-term.

.. note::
  Currently, multi-terms are restricted to 2-multi-terms in most
  parts of Squirrel.

There is no syntactic separation between terms and multi-terms: any
Squirrel term can be a multi-term (though syntactic checks are
performed in some places, when it is necessary that the user provides a
single term).

Squirrel heavily uses multi-terms. Most notably, the equivalence
between two terms :n:`t__1` and :n:`t__2` is written
:term:`equivalence atom` :n:`equiv(@term__bi)`,
where :n:`@term__bi` is any bi-term (i.e. a 2 multi-term) such that
its left (resp. right) projection is :n:`t__1` (resp. :n:`t__1`).
   

Diff-terms
-----------

.. prodn:: 
   diff_term ::= diff(@term, @term)

:n:`diff(@term__1,@term__2)` is a :gdef:`diff-term <diff-term>`
representing a diverging behaviour between the *left* component
:n:`@term__1` and the *right* component :n:`@term__2`.
Currently, diff-terms can only have two components, hence they can only be
used in bi-terms. 


Macros
------

:gdef:`Macros <macro>` are special built-in *probabilistic*
functions defined by induction over the execution trace (i.e. the 
:g:`timestamp` type). 
Applied macros can occur in terms as follows:

.. prodn::
   macro_id ::= @ident
   macro_application ::= @macro_id {* @term} @ @term

The term :n:`@macro_id @term__1 ... @term_n @ @term__t` represents the
application of macro symbol :n:`@macro_id` to arguments
:n:`@term__1 ... @term_n` at a time-point :n:`@term__t` (of type
:g:`timestamp`).

The semantics of a macro symbol :n:`@macro_id` depends on the system
in which it is interpreted:

* its semantics over a :term:`single system`, depends on the system
  definition, see the :ref:`system-defined macros section <section-system-macros>`.

* over a :term:`multi-system` :n:`S__1,...,S__n`, it
  represents a :n:`n` multi-term, whose :n:`i`-th component corresponds to
  the interpretation of the macro over the single system :n:`S__i`.

   
Formulas
========

Squirrel features two kinds of formulas: :term:`local formulas<local
formula>` and :term:`global formulas<global formula>`.

Local formulas
--------------

:gdef:`Local formulas <local formula>` are :term:`terms <term>` of
type :g:`bool`. They correspond to the embedding of a lower-level
logic inside using terms. They can in particular be constructed using
the following (standard and Squirrel-specific) logical constructs:

.. prodn::
  term += @term && @term | @term %|%| @term | @term => @term | not @term
    | happens({+, @term}) 

Boolean connectives for *local* formulas are :n:`&&, ||, =>, not`,
where :n:`&&, ||, =>` are used with a right-associative infix notation.
Concretely, these are all :term:`built-in<built-in>` function symbols.
   
Not all time-points are actually scheduled in an execution trace.
The distinction is made through the :gdef:`happens` predicate:
:n:`happens(@term)` (where :n:`@term`
is of type :g:`timestamp`) states that :n:`@term` has been scheduled.
Then,
:n:`happens(@term__1,...,@term__n)` is syntactic sugar
for :n:`happens(@term__1)&&...&&@happens(term__n)`.

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

A :gdef:`reachability atom` :n:`[@term]` holds if :n:`@term` evaluates to true with overwhelming probability.

An :gdef:`equivalence atom` :n:`@equiv(@term__1,...,@term__n)` is formed
from a sequence of 2-diff-terms. Its meaning is that the sequence of
left projections of the diff-terms is computationally indistinguishable from
the sequence of right projections, i.e. any PPTM adversary has
at most a negligible probability of distinguishing them.

.. note:: Compared to the theoretical presentations of the logic, which do
   not describe diff-terms, Squirrel variables are by default
   multi-term variables, and can be instantiated by diff-terms. 
   When necessary, the :g:`glob` variable tag is forced by the tool to
   forbid diff-terms; this is the case for global quantifications.
