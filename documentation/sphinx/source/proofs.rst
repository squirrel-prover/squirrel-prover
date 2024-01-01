.. _section-proofs:

.. How to write proofs in Squirrel

------
Proofs
------

The proof of a lemma is given after the lemma declaration,
between the :g:`Proof` and :g:`Qed` markers.
It consists in a list of tactics. The invocation of each
tactic modifies the proof state, which contains a list of goals to prove.
Each goal is displayed as a judgement.
Initially, the proof state consists of a single goal, as declared by the
user. Each tactic then reduces the first goal of the proof state to
an arbitrary number of new sub-goals. When no goal is left, the proof
is completed and :g:`Qed` can be used.

The complete list of tactics can be found in the corresponding
:ref:`tactic index <tactic_index>`.

.. _section-judgements:

Judgements
==========

Squirrel features two kinds of judgements:
local judgements and global judgements.

Logical variables
-----------------

:gdef:`Logical variables<logical_var>` are free variables in a current goal. Such variables are implicitly quantified universally based on their type and tags.

Hypotheses
----------

Hypotheses are referred to by a hypothesis identifier :n:`@hypothesis_id`.

.. prodn:: hypothesis_id ::= @ident

Local judgement
---------------

The general layout for a local judgement is as follows:

.. squirreldoc::
   System: currentSystem
   Type variables: tvars
   Variables: vars
   H_1: hypothesis_1
   ...
   H_k: hypothesis_k
   ——————————————
   conclusion

The judgement asserts that the conclusion below the line holds
in the context given above the line.
We now describe the various components of the judgement:

* the system :g:`currentSystem` is a :n:`@system_expr` in which the
  judgement's formulas should be understood;

* :g:`tvars` are the judgement's :ref:`type variables<section-polymorphism>`; 

* :g:`vars` are the judgement's term variables with their types and :term:`tags<tag>`;

* each hypothesis is identified by its hypothesis identifier
  (e.g. :g:`H_1, H_2`) and is either a global hypothesis, whose body is
  a :term:`global formula`, or a local hypothesis, whose body is a
  :term:`local formula`;

* :g:`conclusion` is a :term:`local formula`.


Global judgement
----------------

The general layout for a global judgement is similar to the local one except that now:

 * :g:`currentSystem` is a :n:`@system_context`;

 * all hypotheses, as well as the conclusion, are :term:`global formulas<global formula>`.

When the conclusion is a single :n:`equiv(@term,...,@term)` predicate,
all the bi-terms that need to be proved equivalent are displayed as a
numbered list.

.. example:: Initial judgement for observational equivalence

   Consider a lemma for observational equivalence, where the
   frame is enriched with some public key, as follows:

   .. squirreldoc::

      global lemma [myProtocol] obs_equiv t : [happens(t)] -> equiv(frame@t, pk(sk))

   When starting its proof, after doing :g:`intro H`, the goal that the user must prove is displayed as:

   .. squirreldoc::

      [goal> Focused goal (1/1):
      Systems: left:myProtocol/left, right:myProtocol/right (same for equivalences)
      Variables: t:timestamp[glob]
      H: [happens(t)]
      ----------------------------------------
      0: frame@t
      1: pk (sk)
 
   
Generalities
============

Tactic arguments
----------------

Tactics that apply to judgements whose conclusion is an equivalence
may take a natural number as argument to identify one item in the equivalence.
This is represented using the :token:`position` token.

.. prodn::
  position ::= @natural

Many tactics expecting a term support term :gdef:`patterns<pattern>`,
which are underspecified terms that can include term holes
:g:`_`. Most tactics will match the pattern against
sub-terms of the current goal until it manages to infer values for the term
holes.

Term patterns are produced by appending to the production of
:n:`@term` and :n:`@sterm` the hole construct:

.. prodn:: term_pat ::= ...
           | _
           sterm_pat ::= ...
           | _

  
Intro patterns
~~~~~~~~~~~~~~
  
Introduction patterns are the principal tool used to do proof-context
`book-keeping <https://coq.inria.fr/refman/proof-engine/ssreflect-proof-language.html#bookkeeping>`_.
They are used in Squirrel with an SSReflect-inspired syntax.
For a more comprehensive and detailed guide to introduction patterns, see
`here <https://coq.inria.fr/refman/proof-engine/ssreflect-proof-language.html#introduction-in-the-context>`_.
Note however that Squirrel supports only a sub-set of SSReflect intro
patterns, and that their behaviour in Squirrel may vary in small ways.

Introduction patterns take a different meaning depending
on the tactic in which they are used
(:tacn:`intro`, :tacn:`have`, :tacn:`destruct`, ...). Nonetheless,
a introduction pattern always applies to a set of
focused formulas (sometimes taken in a judgement, with a full
proof-context) which they modify. A introduction pattern may create or
remove focused formulas. Most introduction patterns act only on the top-most
variables or assumptions of the focused formulas (e.g. if the formula
is :g:`forall x. G` or :g:`H => G` then the pattern will start by acting on
:g:`x` or :g:`H`).

.. prodn::
   naming_ip ::= {| _ | ? | @ident }
   and_or_ip ::= {| [] | [ {+ @simpl_ip } ] | [ {+| @simpl_ip } ] }
   simpl_ip ::= {| @naming_ip | @and_or_ip | @rewrite_ip }
   s_item ::= {| // | /= | //= }
   rewrite_ip ::= {| -> | <- }
   expand_ip ::= @/{| @macro_id | @operator_id }
   clear_switch ::= %{ {+ @hypothesis_id} %}
   intro_pat ::= @simpl_ip | @s_item | @expand_ip | @clear_switch | * | >
  
A :gdef:`naming introduction pattern<naming ip>` :n:`@naming_ip` pops
the top-most assumption or universally quantified variable of the
focused formula and introduces it in the proof context,
with a name chosen according to the pattern:

* :n:`@ident`: using the name :n:`@ident` provided, which fails if
  :n:`@ident` is already in use;
* :n:`?`: using a name chosen automatically by Squirrel;
* :n:`_`: using an automatically chosen name for variables, and the
  name :n:`_` for assumptions, which is a special name that can never
  be referred to by the user. Note that, contrary to other
  :n:`@hypothesis_id`, several hypotheses may be named :n:`_`.

A :gdef:`and/or introduction pattern<and or ip>` :n:`@and_or_ip` will,
for each focused formula, destruct the top-most assumption of the formula:

* :n:`[ @simpl_ip ... @simpl_ip ]`: the top-most assumption of the formula must
  be a conjunction with as many conjuncts as simple
  patterns are provided.
  Destruct the conjunction, handling each conjunct according
  to the corresponding :n:`@simpl_ip`.

* :n:`[ @simpl_ip | ... | @simpl_ip ]`: the top-most assumption of the formula
  must be a disjunction with as many disjuncts as simple
  patterns are provided.
  Destruct the disjunction, creating a formula for
  each disjunct and handling each of them according to the
  corresponding :n:`@simpl_ip`.

.. note::
  Existentials are viewed as conjunctions in intro patterns.
  Hence, when the conclusion is of the form :g:`(exists x, phi) => psi`,
  the tactic `intro [x H]` will introduce a variable `x` and hypothesis
  `H : phi`. Here, the conjunctive intro pattern has been used to
  destruct the existentially quantified hypothesis during its introduction.

A :gdef:`simplification item<simplification item>` :n:`@s_item`
simplifies the focused formulas:

* :g:`//` removes all formulas on which :g:`auto` concludes;
* :g:`/=` simplifies all formulas using :tacn:`simpl`;
* :g:`//=` is short-hand for :g:`// /=`;

A :gdef:`rewrite intro pattern item<rewrite ip item>` :n:`@rewrite_ip`
uses the top-most assumption to rewrite the focused formulas. The top
assumption is cleared after rewriting.

* :g:`->` reads the top-most assumption as a left-to-right rewrite rule.
* :g:`<-` reads the top-most assumption as a right-to-left rewrite rule.

An :gdef:`expansion item<expansion item>` :n:`@expand_ip` expands definitions in the focused formulas:

* :n:`@/@macro_id` expands the applications of the macro symbol;
  :n:`@macro_id` whenever it is applied to a time-point that can be
  shown to happen;
* :n:`@/@operator_id` expands the operator :n:`@operator_id`,
  :math:`\beta`-reducing the operator if it is applied.

A :gdef:`clear switch<clear switch>` :n:`@clear_switch` clears the
specified hypotheses from the proof context.


Proof terms
-----------

Proof terms are used by several tactics (see e.g. :tacn:`have` or
:tacn:`apply`) as a convenient way to combine and (partially) apply
hypotheses, axioms or proved lemmas, in order to derive new facts.

.. prodn::
   proof_term ::= @ident {* @pt_arg}
   pt_arg ::= @sterm_pat | @ident | (% @proof_term) | _

In a :n:`@proof_term` or a :n:`@pt_arg`, an identifier :n:`@ident` must
refer to a hypothesis in the current proof context, an axiom or a
previously proved lemma.

Note that the grammar for proof term arguments :token:`pt_arg` is
ambiguous (because of the :token:`ident` and :token:`sterm`
productions). When this happens, Squirrel tries to desambiguate using
the context.

.. note::
   The :n:`(% @proof_term)` syntax is experimental, and is subject to
   change in the future.
   
.. _section-pt-resolution:

Proof-term resolution
~~~~~~~~~~~~~~~~~~~~~

A proof-term :n:`@ident @pt_arg__1 ... @pt_arg__n` is 
resolved into a local or global formula as follows:

* First, the proof-term head :n:`@ident` is resolved as a :n:`@local_formula`
  or :n:`@global_formula` :g:`F`.

* Then, this local or global formula :n:`F` is successively modified
  by applying to it the arguments :n:`@pt_arg__1 ... @pt_arg__n`, in
  order, as follows:

  + :n:`@sterm_pat`: the top-most element of
    :n:`F` must be a universally quantified variable, which is then
    substituted with :n:`@sterm_pat`, e.g. :n:`forall x, F0` is replaced
    with :n:`(F0{x -> @sterm})`.  Moreover, a new term unification
    variable is created for each hole :n:`_` in :n:`@sterm_pat`.

  + :n:`@ident`: the top-most element of :n:`F`
    must be an assumption, which is popped and unified with the formula
    corresponding to the hypothesis, axiom or lemma identified
    by :n:`@ident`.

  + :n:`(% @proof_term)`: the proof-term argument
    :n:`@proof_term` is recursively resolved into a formula, which is
    then unified with the top-most element of :n:`F`.

  + :n:`_`: if :n:`F`'s top-most element is a universally quantified variable
    then a new unification variable is created and applied to :n:`F`.
    If :n:`F`'s top-most element is an assumption :n:`H`, a new sub-goal
    requiring to prove :n:`H` is created and must be discharged by the user.

* Finally, depending on which tactic uses the proof-term, Squirrel
  checks that the term unification variables can all be inferred,
  generalizes the term unification variables that remain, or leaves
  the term unification environment unclosed.

.. todo::
   Charlie: need example

  

In practice, the application of a proof-term argument is more complex
than described above, for several reasons:

* checks must be perfomed to ensure the compatibility of the systems
  corresponding to the applied formulas,
  e.g. applying an axiom over system :g:`[any]`
  to a formula over system :g:`[default]` is valid, but the
  converse is not;

* some formula manipulations occur when trying to mix global and local
  formulas, e.g. when applying a global formula to a local formula.

.. _reduction:

Reduction
---------

Several tactics (e.g., :tacn:`simpl` and :tacn:`auto`) rely on a
reduction engine. This engine repeatedly applies several
transformations, corresponding to the following flags.

.. prodn:: simpl_flags ::= ~flags:[ {*, {| rw | beta | proj | delta | constr } } ]

Leaving the flags unspecified results in the :g:`rw`, :g:`beta` and
:g:`proj` transformations being used. Specifying an empty list of
flags results in no transformations being applied. Otherwise, only the
specified transformations are applied, as described next:

  - :g:`rw`: perform user-defined rewriting;
  - :g:`beta`: perform beta-reductions;
  - :g:`proj`: compute tuple projections;
  - :g:`delta`: replace macros and operators with their definitions;
  - :g:`constr`: automatically simplify trace formulas using
    constraint reasoning.

The :g:`constr` transformation replaces trace (sub-)formulas that
are provably equal to :g:`true` or :g:`false` with that value.
When doing so, the constraint solver takes into account
the current hypotheses but also the conditionals that surround
the trace formula.

The user-defined rewriting transformation eagerly applies the rewrite
rules added to the rewriting database using the :cmd:`hint rewrite`
command.


Automatic simplification tactics
--------------------------------

There are three automated tactics. The :tacn:`autosimpl` tactic is
called automatically after each tactic, unless the tactical
:tacn:`nosimpl` is used.
     
     
.. tacn:: auto {? @simpl_flags}

     Attempt to automatically prove a goal using the hypotheses.

     The tactic uses the :ref:`reduction engine <reduction>`
     with the provided flags (defaults to :g:`rw,beta,proj`).

     Moreover, for local goals, the tactic relies on basic
     propositional reasoning, rewriting simplications, and both
     :tacn:`constraints` and :tacn:`congruence`.

     .. exn:: cannot close goal
        :name: _goalnotclosed

        The current goal could not be closed.


.. tacn:: autosimpl
    
    Simplify a goal, without closing it.

    The tactic uses the :ref:`reduction engine <reduction>`
    with the flags :g:`rw,beta,proj`.

    When the conclusion of the goal is a conjunction, it splits the
    goal into several sub-goals, automatically closing only the trivial
    goals proved by :tacn:`true` and :tacn:`assump`.

    When the conclusion of the goal is a global formula which only contains
    a local formula, the goal is then turned into a local formula. Otherwise
    the tactic does nothing.


.. tacn:: simpl {? @simpl_flags}

     Simplify a goal and its hypotheses.
     This tactic always succeeds, replacing the initial goal with
     a single simplified goal.

     The tactic uses the :ref:`reduction engine <reduction>`
     with the provided flags (defaults to :g:`rw,beta,proj`).

     When the goal is a conjunction, the tactic
     will attempt to automatically prove some conjuncts (using :tacn:`auto`)
     and will then return a simplified sub-goal without these conjuncts.
     In the degenerate case where no conjunct remains, the goal will be :g:`true`.

     When the conclusion of the goal is an equivalence, the tactic
     will automatically perform :tacn:`fa` when at most one of the remaining
     sub-terms is non-deducible. It may thus remove a deducible item
     from the equivalence, or replace an item :g:`<u,v>` with :g:`u`
     if it determines that :g:`v` is deducible.

         
.. _section-tactics:

Tactics
-------

The full syntax of tactic combinations is as follows:

.. prodn::
   tactic ::=  @tactic; {? tac_selector} @tactic
   | @tactic; [ {*| tac_selector @tactic} ]
   | @tactic + @tactic
   | by @tactic   
   | nosimpl @tactic
   | try @tactic
   | repeat @tactic
   | @tactic => {+ @intro_pat}
   tac_selector ::= {*, @natural } :

Tactic combinators behaves as follows:

- the semi-column :g:`;` is used for judgemential composition. The
  second tactic is applied to all sub-goals created by the first one,
  unless the indices of some sub-goals are specified using a
  :n:`@tac_selector`.
- A different tactic can be applied to different sub-goals, for
  example :n:`@tactic; [1: @tactic__1 | 3,4: @tactic__2]` applies
  :n:`@tactic__1` to the first created sub-goal, and :n:`@tactic__2`
  to the third and fourth sub-goals.
- The :g:`+` combinator performs an or-else, i.e. tries applying the
  first tactic, and if that fails, applies the second one.

The remainder behaves as follows:

.. tacn:: by @tactic
    
   Fail unless the tactic closes the goal.

.. tacn:: nosimpl @tactic

  Call the given tactic without the implicit use of simplifications.
  This can be useful to understand what's going on step by step.
  This is also necessary in rare occasions where simplifications are
  actually undesirable to complete the proof.

.. tacn:: try @tactic

  Try to apply the given tactic. If it fails, succeed with the
  sub-goal left unchanged.

.. tacn:: repeat @tactic

  Apply the given tactic, and recursively apply it again on the
  generated sub-goals, until it fails.

.. tacn:: @tactic => @intro_pat_list

   .. prodn:: intro_pat_list ::= {* @intro_pat}

   :n:`@tactic => @intro_pat_list` is equivalent to :n:`@tactic; intro @intro_pat_list`
  
Common errors
-------------

.. exn:: Out of range position.

   Argument does not correspond to a valid equivalence item.

.. exn:: Assumption not over valid system

   Trying to use a proof term that does not apply to the current system.
   

Tactics
=======

Tactics are organized in three categories:

 - :ref:`generic tactics <section-generic-tactics>`, that rely on generic logical reasoning;
 - :ref:`structural tactics <section-structural-tactics>`, that rely on properties of protocols and equality;
 - :ref:`cryptographic tactics <section-crypto-tactics>`, that rely on
   cryptographic assumptions.

In addition, they are also split between tactics applicable to local
goals only, global goals only, or tactics common to both types of
goals. Remark that applying a tactic to a local goal may produce a
global sub-goal, and conversely.

Additionally, there are a few :ref:`utility tactics <section-utility-tactics>` listed at the end.

.. _section-generic-tactics:

Generic tactics
---------------

Common tactics
~~~~~~~~~~~~~~

.. tacn:: admit {? @position}
   :name: admit     

   Admit the current goal, or admit the element at position
   :n:`@position` when the goal is an equivalence.


.. tacn:: assumption {? @hypothesis_id}
   :name: assump
      
    Conclude if the conclusion of the current goal (or :g:`false`) appears in the hypotheses. The
    hypothesis to be checked against may be directly specified using
    :n:`@hypothesis_id`.


.. tacn:: case {| @hypothesis_id | @term_pat}
    
   Perform a case analysis over the given argument:
   
   - :n:`@hypothesis_id`: create one sub-goal for each disjunct of
     :n:`@hypothesis_id`;
   - :n:`@term_pat` a term of type :g:`timestamp`: create one sub-goal
     for each possible :term:`action constructor<action constructor>` of the
     current goal's system
     (all systems appearing in a judgement have the same set of actions,
     as they must be be compatible).
      

.. tacn:: induction {? @term_pat}

   Apply the induction scheme to the conclusion. There are
   several behaviours depending on the type of the current goal
   and whether an argument is given.

   For a reachability goal, if no argument is specified, the
   conclusion must start with a universal quantification over a
   well-founded type and the induction is performed over the
   first quantified variable. If a term is manually
   specified, the goal is first generalized (see
   :tacn:`generalize`) w.r.t. those variables and only then is
   the induction applied.
    
   For an equivalence goal, an argument must always be specified,
   and,
   
    - if a timestamp variable is given then, a weak induction is
      performed over this variable as well as a case disjunction over all
      possible actions;
    - for any other term argument, the
      tactic behaves as in the reachability case.

   The weak induction variant is in fact the most widely used tactic
   in current Squirrel examples to prove the observational equivalence
   of a protocol.

   .. example:: Induction for observational equivalence.

       Over a goal of the form

       .. squirreldoc::

          [goal> Focused goal (1/1):
          Systems: left:myProtocol/left, right:myProtocol/right (same for equivalences)
          Variables: t:timestamp[glob]
          H: [happens(t)]
          ----------------------------------------
          0: frame@t

       Calling :g:`induction t` will apply the weak
       induction and case disjunction,
       yielding as many goals as there are actions
       in the protocol, plus one additional goal for the
       initialization. Assuming an action :g:`A` is in the protocol,
       that has a total of 3 actions, a sub-goal created for the case of :g:`A`
       looks like

       .. squirreldoc::

          [goal> Focused goal (1/4):
          Systems: left:myProtocol/left, right:myProtocol/right (same for equivalences)
          H: [happens(A)]
          IH:  equiv(frame@pred (A))
          ----------------------------------------
          0: frame@A
       
     
.. tacn:: dependent induction {? @variable}
    
    Apply the induction scheme to the conclusion. If no argument is
    specified, the conclusion must be a universal quantification over
    a well-founded type. Alternatively, a term of a well-founded type
    can be given as argument, in which case the goal is first
    generalized in the dependent variant (see :tacn:`generalize
    dependent`) before proceeding with the induction.

    This tactic always uses a strong induction principle (as opposed
    to the :tacn:`induction` tactic, which performs a weak induction
    when the conclusion is an equivalences).
  
.. tacn:: destruct @hypothesis_id {? as @simpl_ip}
    
    Destruct a hypothesis based on its top-most connective
    (existential quantification, disjunction or conjunction), 
    applying the simple introduction pattern :n:`@simpl_ip` to it.

    :n:`@simpl_ip` defaults to :n:`?` if no pattern is provided by the user.
    
    .. example:: Destruct 
       
       If we have the hypothesis :g:`H: A \/ (B /\ C)`, the tactic

       .. squirreldoc::
       
          destruct H as [H1 | [H2 H3]]
          

       removes the :g:`H` hypothesis and creates two sub-goals,
       one with the hypothesis :g:`H1:A`,
       the other with the hypotheses :g:`H2:B, H3:C`.
    
.. tacn:: exists {* @term}
    
    :n:`exists @term__1 ... @term__n` uses the terms :n:`@term__1 ... @term__n` 
    as witnesses to prove an existentially quantified conclusion.

    For example, :g:`exists t` transforms the conclusion of a goal
    :n:`(exists x, phi)` into :n:`(phi{x -> t})`.
    
.. tacn:: generalize {+ @term_pat} {? as {+ @variable}}
   :name: generalize    

   :n:`generalize @term_pat` looks for an instance :n:`@term` of
   :n:`@term_pat` in the goal. Then, it replaces all occurrences of :n:`@term`
   by a fresh universally quantified variable
   (automatically named, or :n:`@variable` if provided).

.. tacn:: generalize dependent {+ @term_pat} {? as {+ @variable}}
   :name: generalize dependent
    
   Same as :n:`generalize`, but also generalize in the proof context.
   All hypotheses in which generalization occurred are pushed back into the
   conclusion before the newly added quantified variables.

.. tacn:: have @have_ip : {|@term|@global_formula}
   
   .. prodn:: have_ip ::= {* @s_item} @simpl_ip {* @s_item}

   :n:`have @have_ip : F` introduces the new hypothesis :n:`F`, which
   can be a :n:`@term` or a :n:`@global_formula`. The new
   hypothesis is processed by :n:`@have_ip` (see below). A new
   sub-goal requiring to prove :n:`F` is created.

   If :n:`@have_ip` is the introduction pattern :n:`@s_item__pre @simpl_ip @s_item__post` then:

   * the simplification item :n:`@s_item__pre` is applied to the *conclusion*
     before adding the hypothesis;

   * the simple intro-pattern :n:`@simpl_ip` is applied to introduce the
     *new hypothesis* :n:`F`;

   * the simplification item :n:`@s_item__post` is applied to the *conclusions*
     after adding the hypothesis.

   It there are mutliple pre or post simplification items, they are
   applied in order.

.. tacn:: assert @term {? as @simpl_ip}
   
   This is an alternative syntax for :n:`have @simpl_ip : @term`,
   where :n:`@simpl_ip` defaults to :g:`?`.

.. tacn:: have @have_ip := @proof_term
   :name: have    

   :n:`have @have_ip := @proof_term` :ref:`resolves <section-pt-resolution>` 
   :n:`@proof_term` --- requiring that the term unification
   enviroment is closed --- and processes the resulting formula using introduction
   pattern :n:`@have_ip`.
        
.. tacn:: apply @proof_term
   :name: apply 
    
   Backward reasoning tactic.
   First, :n:`@proof_term` is :ref:`resolved <section-pt-resolution>` as a
   formula :n:`F__pt`
   --- without closing the term unification environment. 
   Then, it is unified with the conclusion, and finally the term
   unification environment is closed.

   If the unification of :n:`F__pt` with the conclusion fails, the tactic
   introduces
   the top-most element of :n:`F__pt` as described below, and then tries
   again to unify with
   the conclusion:
   
   * if it is a variable (i.e. :n:`F__pt = forall x, F`), it
     introduces a new term
     unification variable :n:`x` and continues from :n:`F`;

   * if it is an assumption (i.e. :n:`F__pt = G => F`), the
     assumption :n:`G` is discharged as a new sub-goal,
     and the tactic continues from :n:`F`.

.. tacn:: apply @proof_term in @hypothesis_id

   Forward reasoning variant of :tacn:`apply`, which unifies the
   premisses of :n:`@proof_term` against the conclusion of
   :n:`@hypothesis_id`, replacing :n:`@hypothesis_id` content with
   :n:`@proof_term`'s conclusion.

   For instance, if :n:`H1:A=>B` and :n:`H2:A`, then :g:`apply H1 in H2`
   replaces
   :n:`H2:A` with :n:`H2:B`. 

.. tacn:: rewrite {* @rw_arg} {? in @rw_target}
    
   .. prodn:: rw_arg ::= {| @s_item | @rw_item }
               rw_item ::= {? {| {? @natural} ! | ?}} {? <-} {| (@proof_term) | /@ident | /( @infix_op) | /*}
               rw_target ::= {| @hypothesis_id | *}
       
   Apply a sequence of :term:`rewriting <rewrite ip item>`
   and :term:`simplification
   <simplification item>` items to the rewrite target, which is:
    
   * the hypothesis :n:`@hypothesis_id` if :n:`rw_target = @hypothesis_id`;
   * all hypotheses if :n:`rw_target = @hypothesis_id`;
   * the conclusion if no specific rewrite target is given.

   :gdef:`Rewrite items <rewrite item>` are applied as follows:

   * proof term rewrite item :n:`@proof_term`:

     + It is first :ref:`resolved <section-pt-resolution>` --- without closing the
       term unification environment --- as a local formula :n:`F` or
       global formula :n:`[F]` where 
       :n:`F = forall x1...xn, H1=>...=>Hn=> l = r`. 
       At that point, :n:`l` and :n:`r` are swapped if the rewrite item is prefixed by :n:`<-`.

     + Then, Squirrel tries to unify :n:`l` with a sub-term of the
       rewrite target, where :n:`x1...xn` are handled as term
       unification variables. If it succeeds, all occurrences of the
       matched instance of :n:`l` are replaced with the corresponding
       instantiation of :n:`r`.
      
     + The term unification environment is closed, and new sub-goals are created 
       for the instantiated assumptions :n:`H1,...,Hn`.

   * expansion items :n:`/@ident` and :n:`/( @infix_op)` tries to expand the corresponding
     symbol (see :term:`expansion item`), while :n:`/*` tries to
     expand all possible symbols;

   * :n:`!` applies the rewrite item as many times as possible, but at least once,
     while :n:`(@natural !)` applies the rewrite item *exactly* :n:`@natural` times.
     :n:`?` behaves as :n:`!`, except that the rewrite item may be applied zero times.
     Otherwise, the rewrite item must be applied exactly once.

   .. exn:: rule bad systems
   
      Rewrite item applies to a system which is not compatible with the rewrite target.
    
   .. exn:: nothing to rewrite
   
      No instance of the rewrite rule were found.
    
   .. exn:: max nested rewriting reached
    
      There were too many nested rewriting. This is to avoid infinite rewriting loops.

.. tacn:: id

   The identity tactic, which does nothing. Sometimes useful when
   using :ref:`tactic combinators<section-tactics>`.
    

.. tacn:: intro {+ @intro_pat}
    
    Introduce the top-most assumptions and universally quantified
    variables of the conclusion as specified by the given introduction
    patterns.

.. tacn:: clear {* @hypothesis_id}
    
    Drop the specified hypotheses. 

.. tacn:: reduce {? @simpl_flags}

     Reduce all terms in a goal, working on both hypotheses and conclusion.
     
     This tactic always succeeds, replacing the initial goal with a
     unique sub-goal (which may be identical to the initial one).

     The tactic uses the :ref:`reduction engine <reduction>`
     with the provided flags (defaults to :g:`rw,beta,proj`).
     
.. tacn:: remember @term_pat

    :tacn:`remember` behaves as :tacn:`generalize`, except that it adds
    as a hypothesis the equality between the generalized term and the
    new variable.
      
       
.. tacn:: revert {* @hypothesis_id}
    
    Remove the hypotheses from the proof context, and add them back
    into the conclusion of the goal.

    For example, running :n:`revert H` on the judgement
    :n:`H : F, Γ ⊢ conc` yields :n:`Γ ⊢ F => conc`.

.. tacn:: left
    
    Reduce a goal with a disjunction conclusion into the goal where the
    conclusion has been replaced with the first disjunct. 
    That is, :tacn:`left` turns :n:`Γ ⊢ F || G` into :n:`Γ ⊢ F`.

.. tacn:: right
    
    Reduce a goal with a disjunction conclusion into the goal where the
    conclusion has been replaced with the second disjunct. 
    That is, :tacn:`right` turns :n:`Γ ⊢ F || G` into :n:`Γ ⊢ G`.

.. tacn:: split
    
    Split a conjunction goal, creating one sub-goal per conjunct.
    For example, :tacn:`split` replaces the goal :n:`⊢ F && G && H`
    with the three goals :n:`⊢ F`, :n:`⊢ G` and :n:`⊢ H`.
       
.. tacn:: use @hypothesis_id {? with {+ @term}} {? as @simpl_ip}
   :name: use     
    
   Instantiate a lemma or hypothesis using the provided arguments (if
   any). An introduction pattern can also be specified to handle the
   new hypothesis.

   .. warning::
      This tactic is a deprecated (and less powerful) variant of the
      :tacn:`have` tactic (with the :n:`have @have_ip := @proof_term`
      form).
      
Local tactics
~~~~~~~~~~~~~

.. tact:: true
   :name: true    
    
   Close a goal when the conclusion is (syntactically) :g:`true`. 

      
Global tactics
~~~~~~~~~~~~~~

.. tace:: byequiv
   :name: byequiv
    
   Transform a global judgement :n:`⊢ [F]` into a local judgement
   :n:`⊢ F`.

.. tace:: constseq @position: {+ (fun @binders => @term) @term}
   :name: constseq

   Simplify a sequence at the given :n:`@position` when it only
   contains a finite number of possible values :g:`v_1`,..., :g:`v_i`
   depending on the value of the sequence variable.

   Given a sequence over a variable of a given type, the arguments
   passed must be of the form :g:`(fun_1 v_1) ... (fun_i v_i)`, where
   all the :g:`fun` functions must be binders over the sequence type
   and must return a boolean.  This tactic creates two sub-goals
   asking to prove the two required properties of the arguments and
   sequence:

   * All the functions must be such that for any given input element,
     exactly one of the functions returns true.
   * The sequence is then expected to be equal to the value of `v_i`
     for all input elements such that fun_i is true.

   .. example::  Constseq one or zero

      Consider the following conclusion for a global goal :g:`0:
      seq(t':timestamp=>(if (t' < t) then one))` (assuming that
      :g:`t'` is a free :g:`timestamp` variable).

      It is clear that this sequence only returns :g:`one` or
      :g:`zero` (zero is in the implicit else branch). It can then be
      simplified by calling the tactic:

      .. squirreldoc::

         constseq 0: 
           (fun (t':timestamp) => t' < t) one) 
              (fun (t':timestamp) => not (t' < t)) zero).

      This replaces in the current goal the constant by zero and one,
      and creats two sub-goal, asking to prove the two following formulas:

      .. squirreldoc::

         forall (t':timestamp),
           (fun (t':timestamp) => t' < t) t'
           || (fun (t':timestamp) => not (t' < t)) t'


      .. squirreldoc::

        (forall (t':timestamp),
           (fun (t':timestamp) => t' < t) t' => if (t' < t) then one = one) &&
        forall (t':timestamp),
           (fun (t':timestamp) => not (t' < t)) t' => if (t' < t) then one = zero


.. tace:: enrich {+, @term}
   :name: enrich

    Enrich the conclusion of an equivalence goal with the given terms.
    Note that this changes the positions of items in the equivalence, and
    if added before other tactics may break later references.

.. tacn:: localize @hypothesis as @simpl_ip

    Change a global hypothesis containing a reachability formula
    :n:`[@term]` to a local hypothesis :n:`@term`, and applies the
    given simple introduction pattern :n:`@simpl_ip` to the new hypothesis.

    For example, the tactic turns :n:`[F],G ⊢ H` into :n:`F,G ⊢ H`.

.. tace:: memseq
   :name: memseq

    Prove that a bi-frame element appears in a sequence of the bi-frame. 

    .. todo::
       Charlie: hum. There are no examples nor test for this function.
       It should be tested before being documented (don't know who did it)


.. tace:: refl
   :name: refl

    Close a goal by reflexivity. Cannot apply if the goal contains
    variable or macros, as those may have different left and right
    behaviours.

.. tace:: sym
   :name: sym

    Swap the left and right system of the equivalence goal.

.. tace:: trans
   :name: trans

    Prove an equivalence by transitivity.

    .. todo::
       Adrien: this deserves an explanation, the tactic actually does a lot.

.. tace:: splitseq @position: (fun @binders => @term)
   :name: splitseq

   Split a sequence according to some boolean test, replacing the
   sequence with two subsequences.

   The function passed as argument must be take as
   argument a variable of the same type as the sequence, and must
   return a boolean.

   .. example:: Splitting a sequence

      Called in a goal with a conclusion of the form :g:`0: seq(x:message =>
      value)`, the tactic:

      .. squirreldoc::

         splitseq 0: (fun y:message => some_test)

      replaces the conclusion with:

      .. squirreldoc::

         0: seq(x:message=>
                  (if  (fun y:message => some_test) x then
                          value))
         1: seq(x:message=>
                  (if not ((fun y:message => some_test) x) then
                          value))


.. _section-structural-tactics:

Structural tactics
------------------

Common tactics
~~~~~~~~~~~~~~

.. tacn:: constraints

     Attempt to conclude by automated reasoning on trace literals.
     Literals are collected from hypotheses, both local and global,
     after the destruction of conjunctions (but no case analysis is
     performed to handle conjunctive hypotheses). If the conclusion
     is a trace literal then it is taken into account as well.


.. tacn:: depends @timestamp, @timestamp

    If the second action depends on the first action, and if the second
    action happens, then add the corresponding timestamp inequality.

    .. exn:: Not dependent

       The two actions are not dependent, i.e. were not derived
       from two outputs in sequence in the source process.

.. tacn:: expand {+, @macro_id | @macro_application }
    
    Expand all occurences of the given macros in both the conclusion
    and proof-context, either fully specified with an action or simply
    a type of macro.
    
.. tacn:: expandall
    
    Expand all possible macros in the current proof-context and conclusion. 
             

.. tacn:: fa {|@position | {+, @fa_arg}}
   :name: fa
    
   .. prodn::
      fa_arg ::= {? {| ! | ?}} @term_pat

   Apply the function application rule, simplifying the goal by
   removing the head function symbol, as follows:
   
   * in a local goal with conclusion :g:`f u = f v`, the conclusion is
     replaced with :g:`u=v`. This produces as many sub-goals as there are arguments
     of the head function symbol. For a local goal, the tactic takes no
     arguments.
   * in a global goal, :g:`f(u1,...,un)` is replaced with :g:`u1,...,un`.

     
   In the global goal setting, the target can be selected with its
   :n:`@position`, or using a :n:`@fa_arg`, which behave as follow:

   * :g:`fa` :n:`@term_pat` selects the first position in the equivalence
     that matches :n:`@term_pat`.
   * :g:`fa !t` repeats the function application as many times
     as possible, but at least once.
   * :g:`fa ?t` repeats the function application as many times
     as possible, including 0.
   * :g:`fa arg1, arg2, ...` is syntactic sugar for
     :g:`fa arg1; fa arg2; ...`.
   
   .. todo::
      `fa` reachability does not behave as described. Also, it seems
      useless to me now, except for `try find` constructs.
      Finally, `fa` reach takes no arguments.

.. tacn:: namelength @term, @term
    
    Adds the fact that two names have the same
    length. The two arguments must the indeed be a :decl:`name`.

    .. warning::
       This tactic is deprecated. Use the :term:`namelength axiom` instead.

      
Local tactics
~~~~~~~~~~~~~



.. tact:: congruence
   :name: congruence     

   Attempt to conclude by automated reasoning on message (dis)-equalities.
   Equalities and disequalities are collected from hypotheses, both local 
   and global, after the destruction of conjunctions (but no case analysis 
   is performed to handle conjunctive hypotheses). If the conclusion
   is a message (dis)-equality then it is taken into account as well.

.. tact:: const @variable
   :name: const
    
   Add the `const` tag to a variable.

   The variable must be of a finite and fixed (η-independent) type,
   and must not appear in any global hypothesis (some global
   hypotheses may be localised (see :tacn:`localize`) if necessary.

.. tact:: eqnames
   :name: eqnames
    
    Add index constraints resulting from names equalities,
    modulo the known equalities.
     
    If :g:`n[i] = n[j]` then :g:`i = j`. This is checked on all name
    equality entailed by the current context.

.. tact:: eqtrace
   :name: eqtrace

    Add term constraints resulting from timestamp and index
    equalities. 

    Whenever :g:`i=j` or :g:`ts=ts'`, we can substitute one by another
    in the other terms.

.. tact:: executable @term
   :name: executable
    
    Assert that :g:`exec@_` implies :g:`exec@_` for all previous
    timestamps. 

    Given as input a timestamp :g:`ts`, this tactic produces two new
    sub-goals, requiring to prove that :g:`happens(ts)` holds and that
    :g:`exec@ts` also holds. The fact that :g:`(forall (t:timestamp),
    t <= ts => exec@t)` is added as a hypothesis to the current goal.


.. tact:: project
   :name: project
    
    Turn a local goal on a :term:`multi-system` into one goal for each
    single system in the multi-system.

.. tact:: rewrite equiv {? -}@proof_term
   :name: rewrite_equiv
    
    Use an equivalence to rewrite a reachability goal.

    First, try to resolve :n:`@proof_term` as an equivalence
    :g:`equiv (diff(u,v))`. Then, try to find a context :g:`C`
    that does not contain any :decl:`names<name>`, :term:`diff-terms<diff-term>`
    or :term:`macro terms<macro>` such that the current local goal :g:`phi` is
    convertible with :g:`C[u]`. If such a context is found, the current goal is
    is changed to :g:`C[v]`.

    If a :g:`-` sign is added in front of :n:`@proof_term`, the
    rewriting occurs in the other direction, replacing :g:`v` with
    :g:`u`.

    .. example:: Hash rewrite

       Consider the following goal.

       .. squirreldoc::
          [goal> Focused goal (1/1):
          System: default/left (equivalences: left:default/left, right:default/right)
          H: equiv(diff(h (a, k), n), diff(h (b, k), m))
          U: [a <> b]
          ----------------------------------------
          h (a, k) <> h (b, k)

       Assuming we have been able to prove that two hashes are
       indistinguishable from names, we have hypothesis :g:`H`. We
       then use :g:`H` to replace the hashes with names in the conclusion
       of the goal, where we want to prove that the two hashes are not equal.

       Calling :g:`rewrite equiv H` produces the new goal:
       
       .. squirreldoc::
          [goal> Focused goal (1/1):
          System: default/right (equivalences: left:default/left, right:default/right)
          H: equiv(diff(h (a, k), n), diff(h (b, k), m))
          U: [a <> b]
          ----------------------------------------
          n <> m

.. tact:: slowsmt
   :name: slowsmt
    
    Version of the :tacn:`smt` tactic with higher time limit. 
      
.. tact:: smt
   :name: smt
    
    Try to discharge the current goal using an SMT solver. 
      

.. tact:: subst @term, @term
   :name: subst

    If :g:`x = t` where :g:`x` is a variable, then :g:`subst x, t`
    substitutes all occurrences of :g:`x` with :g:`t` and removes :g:`x`
    from the :term:`logical variables <logical_var>`.

    .. exn:: Unequal arguments

       Terms given as argument are not equal.
       
    
    
Global tactics
~~~~~~~~~~~~~~



.. tace:: cs @pattern {? in @position}
   :name: case_study

   Performs case study on conditionals inside an equivalence.

   Without a specific target, :g:`cs phi` will project all conditionals
   on phi in the equivalence. With a specific target, :g:`cs phi in i`
   will only project conditionals in the i-th item of the equivalence.

   .. example::

     When proving an equivalence

     .. squirreldoc::
        equiv(if phi then t1 else t2, if phi then u1 else u2)
        
     invoking :g:`cs phi` results in two sub-goals:

     .. squirreldoc::
        equiv(phi, t1, u1)
        equiv(phi, t2, u2)

   .. exn:: Argument of cs should match a boolean.
      :undocumented:

   .. exn:: Did not find any conditional to analyze.
      :undocumented:

.. tace:: deduce {? @position}
   :name: deduce

   :g:`deduce i` removes the :g:`i`'th element from the bi-frame when it can
   be computed from the rest of the bi-frame. Without any argument, it
   will remove the first element that can be dropped, if it
   exists.

   Here, the fact that the bi-frame element :g:`u` can be computed
   from the other bi-frame elements :g:`x,y,...` means that there
   exists a context :g:`C` made of function applications such that
   :g:`u` is equal to :g:`C[x,y,..]`.

   This relies on some heuristical automated reasoning. Some properties on
   macros are automatically exploited, e.g. that for any
   timestamp :g:`t`, :g:`frame@pred(t)` allows to deduce
   :g:`input@t`, all :g:`frame@t'` for :g:`t' < pred(t)`, as well as
   the :g:`output@t'` for whenever :g:`exec@t'` is true.

   .. todo::
      Charlie: do we want an exhaustive description of the deduce algo?
      
      Adrien: without arguments, it removes all elements that can be
      dropped I think.

.. tace:: diffeq
   :name: diffeq

   Close a reflexive goal up to equality. That is, if all diff-term
   whitin the global goal's conclusion always evaluate to the same value in all
   systems, the equivalence holds. For each diff-term, a
   dedicated sub-goal is created.

   .. warning:: This tactic is still at an experimental development
       stage. We do not recommend its usage.     

.. _section-crypto-tactics:

Cryptographic tactics
---------------------

Cryptographic tactics enable reasoning over cryptographic and
probabilistic properties of random samplings and primitives.

Occurrence formula
~~~~~~~~~~~~~~~~~~

Several reasoning techniques require tracking how a given name is
used. For instance, if the name :g:`n` does not occur at all in term
:g:`t`, then :g:`n=t` is false with overwhelming probability. To apply
a cryptographic assumption relying on a secret key, one needs to check
that all occurrences of the secret key are valid (i.e. correspond
to the key argument of the corresponding primitive).

Over macro-free terms, collecting occurrences is simply equivalent to
looking at the subterms. However, if some macros occur in :g:`t`,
typically :g:`input@ts` or :g:`output@ts`, we need to look through all
the actions that may have happened before :g:`ts` to look for
occurrences.

We define here how to build an :gdef:`occurrence formula` that will be
reused in several tactics description. For any name :g:`n`, any term
:g:`t` and a set of allowed patterns :g:`pats` (patterns built over
the name :g:`n` and function applications), we define the formula
:g:`occurs(n,t,pats)` as the conjunction of conditions under which it
is possible that :g:`n` occurs in :g:`t` without following one of the
allowed pattern of `pats`:

* whenever :g:`t` contains as a subterm an occurrence :g:`n` that does
  not match any of the allowed patterns :g:`pats`, the formula is
  :g:`true`.
* whenever :g:`t` contains a :ref:`system-defined
  macro<section-system-macros>`, :g:`macro@ts`, if `ts` is a concrete
  action, we simply unfold the definition of the macro, and whenever
  is it not concrete, we collect all actions of the form :g:`A1` such
  that :g:`n` occurs in the definition of the action not as an allowed
  pattern, and the formula :g:`A1<=ts` is added to the conjunction of
  :g:`occurs(n,t,pats)`.

:g:`occurs` is of course generally defined for indexed names that may
occur in indexed actions.

.. example:: Basic name occurrence

   Consider the following process:

   .. squirreldoc::
      name n : index->message

      channel c

      system (!_i !_j A : out(c,n(i)) | B :in(c,x);out(c,x)).

      
   The formula :g:`occurs(n(i),input@B,none)` is equal to :g:`exists j. A(i,j) < B`.  


.. example:: Key corruption
       
   Consider the following process:

   .. squirreldoc::
      name k : message
      name r : message

      senc enc,dec.
      
      channel c.

      system (Corr: out(c,k) | B : in(c,x);out(c,enc(x,r,k))).

      
   To reason about the encrypted message, the key :g:`k` needs to be
   secret, and thus the dynamic corruption should not have
   happened. This intuition is captured by the formula
   :g:`occurs(k,input@B,enc(_,r,k))`, which is equal to :g:`Corr < B`.

   
This formula may be imprecise, for example due to states.

.. example:: Imprecise state occurrence

   .. squirreldoc::
      name n : message

      mutable s = n.
      
      channel c

      system (A: out(c,s) | B :in(c,x);out(c,x)).

   Here, :g:`n` occurs only inside the :g:`init` action, where the
   mutable state is initialized with value :g:`n`. The formula
   :g:`occurs(n,input@B,none)` is then equal to :g:`init < B`.
   However, the occurrence can happen only if :g:`A` did occur between
   :g:`init` and :g:`B` to reveal the value of the state.


We define a precise variant :g:`precise_occurs(n,t,pats)`, that tracks
more precisely the usages of the states, and also adds the condition
that the correct value of the state is revealed if a state can contain
an occurrence of :g:`n`.

We also generalize occur to allow for collecting multiple name
occurrences at once, which is useful when we want to allow patterns depending on
two names at once (see e.g. :tacn:`gdh` or :tacn:`ddh`).

.. todo::
   Adrien: how name occurrences are computed is quite complicated, and
   more involved than what is described here I think (conditions,
   source terms, occurrences below bound variables, fold-macro-support
   shenanigans and tomfoolery, ...)

   I think we need to settle ourselves for an intuitive description
   with examples, while making clear that this is a partial
   description.

Common tactics
~~~~~~~~~~~~~~


.. tacn:: fresh {? ~precise_ts} {| @position | @hypothesis_id }
   :name: fresh

   Fresh is an information-theoretically sound tactic exploiting the
   fact that names represent independent random samplings. This can be
   exploited in two ways: i) to remove a fresh name from an
   equivalence; or ii) to obtain that a term has a negligible
   probability of being equal to a fresh name.

   .. todo::
      Adrien: could not finish reading. A note:
      I see no mention of the `large` assumption on types.
   
   In a local goal with conclusion :g:`phi`,
   the tactic may be called on a hypothesis of the form :g:`t=n` for
   some name :g:`n` sampled over a type with tag :g:`large`.
   For such a sampling, if term :g:`t` is computed without knowing :g:`n`,
   this equality can only hold with negligible probability.
   We may thus assume that :g:`n` occurs in :g:`t`.
   Accordingly, the tactic turns the conclusion
   into the formula :g:`occur(n,t,none) => phi` (see the
   definition of the :term:`occurrence formula`).

   If one can then prove that :g:`n` cannot occur in :g:`t`, that is
   that :g:`occur(n,t,none)` is false, that new conclusion trivially holds.
   If :g:`occur(n,t,none)` is trivially false, e.g. if
   :g:`t` is a macro-free term without :g:`n` as a subterm, the goal
   will be directly closed.


   .. example:: Name leak

      Consider a small process :g:`in(c,x); A : out(c,x);in(c,x); B:
      out(c,n)`, where we wish to prove that :g:`input@A <>
      n`. Intuitively, this holds as :g:`n` is only revealed after
      :g:`A` has occurred.

      The goal corresponding to this proof will look like this:

      .. squirreldoc::
         [goal> Focused goal (1/1):
         System: left:default/left, right:default/right
         Eq: input@A = n
         H: happens(A)
         ----------------------------------------
         false

      Calling :g:`fresh Eq` turns the goal into:

      .. squirreldoc::
         [goal> Focused goal (1/1):
         System: left:default/left, right:default/right
         Eq: input@A = n
         H: happens(A)
         ----------------------------------------
         B < A => false

      Here, Squirrel automatically deduced that :g:`n` can only occur
      inside :g:`input@A` if the output of :g:`B` happened before
      :g:`A`. One would conclude by using the fact, according to the
      process definition, this is impossible.
      
   In an equivalence goal, on the other hand, the tactic must be applied to a bi-frame
   element :g:`i` of the form :g:`diff(nL,nR)`, where :g:`nL`, :g:`nR` are names
   sampled over the same type.
   Since samplings are independent, the two names are indistinguishable,
   unless some information on them is revealed by the rest of the bi-frame.
   Note that, contrary to the local case, that property holds even if the type
   is not :g:`large`.

   If we let :g:`bf` denote the bi-frame, the :g:ì`th 
   bi-frame element is replaced by the tactic with

   .. squirreldoc::
      if not(diff(occur(nL,bf,i : diff(nL,nR)),occur(nR,bf,i : diff(nL,nR)))) then
        zero
      else
        diff(nL,nR)

   We specify through the occurrence formula that the only possible
   occurrence of :g:`nL` is in fact the one we are currently looking at.

   In all cases, the :g:`precise_ts` makes the tactic use
   `precise_occur` instead of `occur`.

   Latest formal Squirrel description: :cite:`bkl23hal` (Appendix F).

Local tactics
~~~~~~~~~~~~~


.. tact:: cdh @hypothesis_id, @term
   :name: cdh

   This tactic applies the Computational Diffie-Hellman assumption (see
   e.g. :cite:`okamoto2001gap`), stating
   for a generator :math:`g` and randomly sampled exponents :math:`a` and :math:`b`,
   it is computationally hard to compute :math:`g^{ab}`
   when only :math:`g^a` and :math:`g^b` are known.

   A :g:`cdh`, :g:`ddh` or :g:`gdh`
   :term:`group declaration <group declaration>` must have been
   specified (the DDH or GDH assumptions indeed both imply the CDH assumption).
   For a group with generator :g:`g` and exponentiation
   :g:`^`, the tactic :g:`cdh M, g` may be called in a local goal on
   a message equality hypothesis :g:`M` of the form `t=g^{a b}`.
   Following the CDH assumption, :g:`M` can only hold if :g:`t`
   accesses :g:`a` or :g:`b` in some way other than :g:`g^a` and :g:`g^b`.

   Therefore, the tactic will replace in the current goal the conclusion :g:`phi` with
   :g:`occur(a,t,g^a) || occur(b,t,g^b) => phi` (see the
   definition of the :term:`occurrence formula`). If both occurrence formulas are
   trivially false, then the goal is closed automatically.
    
   A formal description of this tactic has not yet been given in any
   published work.

.. tact:: gdh @hypothesis_id, @term
   :name: gdh

   This tactic applies the Gap Diffie-Hellman assumption (see
   e.g. :cite:`okamoto2001gap`), which is similar to CDH over :math:`g^a`
   and :math:`g^b`, except that the attacker is additionally allowed to access an oracle
   testing equality to :math:`g^{ab}`. It also includes the Square-GDH
   variant (see :cite:`fujioka2011designing`), which is equivalent to the GDH
   assumption for prime order groups, where the attacker can also test
   equality to :math:`g^{aa}` and :math:`g^{bb}`.

   A :g:`gdh` :term:`group declaration <group declaration>` must have been
   specified.

   The behaviour of this tactic is similar to :tacn:`cdh`, expect that
   the current goal's conclusion :g:`phi` is replaced with a more permissive formula
   :g:`occur((a,b),t,(g^a,g^b,_=g^(ab), _=g^(bb), _=g^(aa)) => phi`
   (see the definition of the :term:`occurrence formula`).

   A formal description of this tactic has not yet been given in any
   published work.

.. tact:: collision
   :name: collision
    
   Requires a :term:`hash function declaration <hash function>`.

   This tactic applies the known-key collision resistance assumption
   (see e.g. the cr2-kk assumption from
   :cite:`goldwasser1996lecture`).
    
   It collects all equalities between hashes occurring at top-level in
   message hypotheses, that is all hypotheses of the form
   :g:`h(u,k)=h(v,k)`, and for each such hypothesis adds as new
   hypothesis :g:`u=v`.

   As this implements the known-key variant of the collision resistance assumption,
   no side condition is checked on the hash key.

   Latest formal Squirrel description: :cite:`bkl23hal` (only as an example).       

.. tact:: euf @hypothesis_id
   :name: euf
    
   Requires either a :term:`hash function` or a :term:`signature
   scheme` declaration.

   This tactic applies the EUF-CMA axiom in a local goal, either for keyed-hashes or
   signatures. (see e.g. :cite:`goldwasser1996lecture`)

   For a hash function :g:`h(x,k)`, one may call :g:`euf M` over a
   message equality :g:`M` of the form :g:`t = h(m,k)` or
   :g:`h(m,k)=t`. EUF-CMA then states that, provided
   the key :g:`k` is always used in correct position,
   :g:`M` can only hold if computing :g:`t` requires already knowing the hash of :g:`m`.
   Accordingly, the tactic creates a first new sub-goal asking
   to prove that the key is only used in correct position, i.e.
   a sub-goal with conclusion :g:`not(occur(k,goal,h(_,k))` (see the
   definition of the :term:`occurrence formula`).
   The tactic then collects all possible occurrence of a honest hash :g:`h(u,k)` inside
   :g:`t`, and for each of them, creates a sub-goal with the original conclusion
   and a new hypothesis stating that :g:`m=u`. Moreover, if the occurrence is
   under a macro, additional new hypotheses will state that these macros must be taken
   at an earlier timestamp than :g:`t`.

   .. example:: Basic hashing
    
      Consider the following system:
      
      .. squirreldoc::
         hash h
         name k:message
         channel c
         name n : message
         name m : message
      
         system (!_i out(c,h(n,k)) | in(c,x);out(c,x)).

      Calling :g:`euf` over a hypothesis of the form :g:`input@tau <>
      h(m,k)` would add the fact that :g:`h(m,k)` needs to be equal
      to one of the honestly computed hashes appearing in
      :g:`input@tau`, which are all of the form :g:`h(n,k)`. The new
      hypothesis would then be:

      .. squirreldoc::
        (exists (i:index), A(i) < tau && m = n)
   
   For a signature function :g:`sign(x,r,k)`, public key :g:`pk(k)`
   and verification function :g:`check(s,m,pub)`, :g:`euf` must be called
   on a hypothesis of the form :g:`check(s,m,pk(k))`. The behaviour
   is then similar to the hash case: honest signatures that may occur
   in :g:`s` will be collected, and :g:`m` must be equal to one of the
   honestly signed messages. A sub-goal for each possible honest signing
   case is created, as well as a sub-goal specifying that the key is
   correctly used, i.e. with conclusion
   :g:`not(occur(k,goal,sign(_,k), pk(k))`.
    
   Latest formal Squirrel description: :cite:`bkl23hal`.

.. tact:: intctxt @hypothesis_id
   :name: intctxt
    
   This tactic applies the INT-CTXT assumption (see
   e.g. :cite:`bellare2000authenticated`) in a local goal.

   It requires the declaration of a :term:`symmetric encryption` scheme.
   
   It can be applied to a hypothesis either of the form
   :g:`dec(c,k)<>fail` or :g:`dec(c,k) = t` (in the latter case,
   it will generate as an additional proof obligation that `t <> fail`).

   The INT-CTXT assumption then states that, provided the key :g:`k`
   is correctly used, such a decryption may only succeed if
   :g:`c` was produced by an honest encryption.

   In both cases, Squirrel will thus collect all honest encryptions made
   with key :g:`k`, and produce a subogal corresponding to each case
   where :g:`c` is equal to one of those honest encryptions.

   The key :g:`k` must only be used in key position, so a sub-goal
   asking to prove that :g:`not(occur(k,c,(enc(_,_,k),dec(_,k)))` is
   created when it is not trivially true (see the definition of the
   :term:`occurrence formula`).

   In addition, a goal asking to prove that all randomness used for
   encryption are disjoint and fresh (when it is not trivially true).

   Latest formal Squirrel description: :cite:`bdjkm21sp`.      


Global tactics
~~~~~~~~~~~~~~

.. tace:: cca1 @position
   :name: cca1
    
   This tactic applies the IND-CCA assumption (see
   e.g. :cite:`bellare2000authenticated`) in a global goal.

   It requires the declaration of a :term:`symmetric encryption` or
   :term:`asymmetric encryption` scheme.

   The tactic may be called over a bi-frame element containing a term of
   the form :g:`C[enc(n, r, m)]`, where
        
   • :g:`r` must be a fresh name;
   • there is no decryption in :g:`C`;
   • no universal message variable occurs;
   • :g:`m` is  a key  or a public key that 
     only appears in key position, i.e. under :g:`pk`, :g:`dec` or
     :g:`enc`.    

   The tactic will then replace the encryption occurrence by an
   encryption of a bitstring of zeroes of the correct length,
   yielding :g:`C[enc(zeroes(len(n)), r, pk(k))]`.


   In addition, the tactic creates a sub-goal asking to prove that all
   occurrences of the key and encryptions are correct. Notably, one
   must prove that :g:`occur(k,bi-frame,(enc(_,_,k), dec(_,k))` (see
   the definition of the :term:`occurrence formula`) is false (or
   :g:`occur(k,bi-frame,(pk(k), dec(_,k))`) for the asymmetric case).

   In addition, in the asymmetric case, a sub-goal is created to prove the
   freshness of the random used in the encryption, with the conclusion
   :g:`occur(r,bi-frame,enc(n,r,m))`.

   In the symmetric case, an additional sub-goal is created ensuring
   that all encryptions are made with distinct fresh randoms (and not
   just the the encryption we are looking at).

   Latest formal Squirrel description::cite:`bkl23hal`.  
    
.. tace:: ddh @term, @term, @term, @term
   :name: ddh


   This tactic applies the Decisional Diffie-Helman assumption (see
   e.g. :cite:`okamoto2001gap`), stating that for a generator :math:`g`,
   and randomly sampled exponents :math:`a`, :math:`b`, :math:`c`, it
   is computationally hard to distinguish :math:`g^{ab}` from :math:`g^c`,
   when only :math:`g^a` and :math:`g^b` are known.
   

   A :g:`ddh` :term:`group declaration <group declaration>` must have been
   specified.

   When calling, :g:`ddh g,a,b,k`, the goal must contain only diff
   terms of the form :g:`diff(g^(ab),g^(c)))`. The tactic will close
   the goal if the formula
   :g:`occur((a,b,c),goal,(g^a,g^b,diff(g^(ab),c)))` instantly reduces
   to false (see the definition of the :term:`occurrence formula`).

   Latest formal Squirrel description: :cite:`bdjkm21sp`.
       
.. tace:: enckp @position {? @term_pat } {? @term }
   :name: enckp

   ENC-KP assumes that a symmetric or an asymmetric encryption scheme
   does not leak any information about the public (or secret) key
   used to encrypt the plaintext. It is based on the IK-CPA notion of
   :cite:`bellare2001key`.

   The tactic can be called on a bi-frame element containing a term of
   the form :g:`C[enc(n, r, m)]`, where
        
   • :g:`r` must be a fresh name;
   • there is no decryption in :g:`C`;
   • no universal message variable occurs;
   • :g:`m` is either a key or the diff of two keys, that
     only appear in key position, i.e. under :g:`pk`, :g:`dec` or
     :g:`enc`;
   • if :g:`m` is a key, and a second key has been given as argument to the
     tactic, that key must also occur only in key position.

   When :g:`m` is the diff of two keys, the diff is simplified by keeping
   only the key on the left. When :g:`m` is just one key, a new key with
   which it is replaced can be specified as arugment.
   
   .. example:: Basic ENC-KP application
   
      On a bi-frame element of the form
      
      .. squirreldoc::
         i : enc(n,r,diff(pk(k1),pk(k2)))
   
      calling the tactic :g:`enckp i` will simplify the bi-frame
      element by only keeping the key on the left, yielding
      
      .. squirreldoc::
         i: enc(n,r,pk(k1))

   The tactic expects as arguments:
   
   • the position identifying the bi-frame element;
   • optional: the encryption term on which to apply the tactic;
   • optional: the new key with which to replace the key.


   .. example:: Switching key with ENC-KP
    
      On a bi-frame element of the form
      
      .. squirreldoc::   
         i: enc(n,r,m)

      the tactic :g:`enckp i, k` will simplify the bi-frame element by using the specified
      key, yielding
      
      .. squirreldoc::
         i: enc(n,r,pk(k))


   .. example:: Targeted ENC-KP application
       
      On a bi-frame element of the form
      
      .. squirreldoc::
         i: ⟨ enc(n,r,m),m'⟩

      the tactic :g:`enckp i,enc(n,r,m), k` will simplify the bi-frame
      element by using the specified key, yielding
      
      .. squirreldoc::
         i: ⟨ enc(n,r,pk(k)),m '⟩


   To apply the enckp tactic, the key :g:`k` must be such that
   :g:`occur(k,bi-frame,(enc(_,_,k), dec(_,k))` (see the definition of
   the :term:`occurrence formula`) is trivially false. (or
   :g:`occur(k,bi-frame,(pk(k), dec(_,k))`) for the asymmetric case).

   When it is not trivially true, a sub-goal is created, asking to prove the
   freshness of the random used in the encryption, with the conclusion
   :g:`occur(r,bi-frame,enc(n,r,m))`.

   In the symmetric case, an additional check is performed ensuring
   that all encryptions are made with distinct fresh randoms (and not
   just the encryption we are looking at).
   
   Latest formal Squirrel description::cite:`bdjkm21sp`.
      
.. tace:: prf @position {? , @term_pat}
   :name: prf

   This tactic applies the PRF assumption (see
   e.g. :cite:`goldwasser1996lecture`).

   It requires a :term:`hash function` declaration.

   This tactic applied to a bi-frame element containg a hash
   application :g:`h(m,k)` tries to replace the hash value with a fresh
   name, under the condition that :g:`m` has never been hashed before,
   and that the key :g:`k` is correctly used.


   Formally, when called over a bi-frame element :g:`i : C[h(m,k)]`,
   the tactic replaces in the current goal the element with :g:`i :
   C[nPRF]` where :g:`nPRF` is a newly generated unique name. It in
   addition produces sub-goals requiring to prove the side
   conditions described above. It notably produces a goal asking to prove that the key
   is only used in key position, i.e. that
   :g:`occur(k,bi-frame,h(_,k))` is false (see the definition of the
   :term:`occurrence formula`). In addition, it creates for each
   occurrence of :g:`h(t,k)` within the bi-frame (that may occur under
   macros) a sub-goal asking to prove that :g:`t <> m`, that is, that
   :g:`m` was never hashed before. Such sub-goals may need to be
   created separately for both projections of the bi-frame.

   .. example:: Basic PRF application

      Consider the following system:

      .. squirreldoc::
         channel c
         hash h
         name k : message
         name n :message
         name m :message
         name p :message
         system (A: out(c,h(n,k)) | B: out(c,h(m,k))).

      When trying to prove that :g:`[happens(A)] ->
      equiv(frame@pred(A),diff(output@A,p))`, one may call the tactic
      prf on the bi-frame element corresponding to the
      :g:`diff(output@A,p)`, which after expanding output is
      :g:`diff(h(n,k),p)`.

      This replaces in the current goal the hash occurrence with
      :g:`diff(n_PRf,p)`, and creates a sub-goal asking to prove that
      the hash message :g:`n` is different from any possible
      previously hashed message. Here, the only other possible hash
      would occur in :g:`frame@pred(A)`, in the output of :g:`B` if it
      occurred before :g:`A`. The created sub-goal then asks to prove
      that :g:`[B < A => n <> m]`.


   If multiple occurrences of hashes occur in the bi-frame element, the
   first one is targeted by default. Calling the tactic with an
   optional :n:`@term_pat` allows to target a specific hash occurrence.

   Latest formal Squirrel description: :cite:`bkl23hal`.

.. tace:: xor @position {? , @term_pat} {? , @term_pat}
   :name: xor

   This tactic applies the unconditionally sound one time pad property
   of the xor operation.

   The tactic applied to a bi-frame element of the form :g:`i : C[n XOR
   t]` will replace the XOR term by

   .. squirreldoc::
      if occur(n,bi-frame, i : C[n XOR t] ) && len(n) = len(t) then n_FRESH else (n XOR t)

   This new term then allows us to drop the old term only if :g:`n` and
   :g:`t` do have the same length (as the one time pad does not work otherwise),
   and if this is the only occurrence of :g:`n` in the
   bi-frame.

   When multiple XOR occur in the bi-frame, one can specify one or two
   optional term patterns, to specify in any order the name :g:`n` or
   the full XOR-ed term :g:`n XOR t` to target.    

   Latest formal Squirrel description: :cite:`bdjkm21sp`.

.. _section-utility-tactics:
  
Utility tactics
---------------


.. tacn:: help {? {|@tacn|concise}}
    
    When used without arguments, display all available commands.
    The tactic can  also display the details for a given tactic name, or display or
    more concise list. It is a tactic and not a command, and as such can only
    be used inside proofs.

.. tacn:: lemmas
    
    Print all axioms and proved lemmas. This is useful to know which lemmas can
    be used through the :tacn:`use` or :tacn:`apply` tactics.

.. tacn:: show @term_pat
    
    Print the messages given as argument. Can be used to print the values
    matching a pattern. 
      
