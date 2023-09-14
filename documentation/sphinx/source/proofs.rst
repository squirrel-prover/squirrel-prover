.. _section-proofs:

.. How to write proofs in Squirrel

------
Proofs
------

The proof of a goal is given after the goal
between the :g:`Proof` and :g:`Qed` markers.
It consists in a list of tactics. The invokation of each
tactic modifies the proof state, which contains a list of goals to prove.
Each goal is displayed as a judgment displaying its current state.
Initially, the proof state consists of a single goal, as declared by the
user. Each tactic then reduces the first goal of the proof state to
an arbitrary number of new subgoals. When no goal is left, the proof
is completed and :g:`Qed` can be used.

The complete list of tactics can be found in the corresponding
:ref:`tactic index <tactic_index>`.

.. _section-judgements:

Judgements
==========

Squirrel features two kind of judgements: local judgement and global judgement.

Logical variables
-----------------

:gdef:`Logical variable <logical_var>` are free variables in a current goal. Such variables are implicitly quantified based on their type and tag.

Hypotheses
----------

.. prodn:: hypothesis_id ::= @ident

Hypotheses are referred to by an hypothesis identifier :n:`@hypothesis_id`
   
Local judgement
---------------

The general layout for a local judgement is as follows:

.. squirreldoc::
   [goal> Focused goal (x/N):
   System: currentSystem
   Type variables: tvars
   Variables: vars
   H_1: formula_1
   ...
   H_k: formula_k
   ——————————————
   goal

The goal is the formula displayed below the horizontal line, while
everything above the line is the proof-context.
We now describe the various components of the judgement:

* we are proving the goal number :g:`x` out of :g:`N` goals;

* the system :g:`currentSystem` of the current judgement is a :n:`@system_expr`;

* :g:`tvars` are the judgement's :ref:`type variables<section-polymorphism>`; 

* :g:`vars` are the judgement's term variables with their types and :term:`tags<tag>`;

* each hypothesis is identified by its hypothesis identifier
  (e.g. :g:`H_1, H_2`) and is either a global hypothesis whose body is
  a :term:`global formula` or a local hypothesis whose body is a
  :term:`local formula`;

* the goal :g:`conc` is a :term:`local formula`.


Global judgement
----------------

The general layout for a global judgement is similar to the local one except that now:

 * :g:`currentSystem` is a :n:`@system_context`;

 * all hypotheses, as well as the goal, are :term:`global formulas<global formula>`.

When the goal is a single :n:`equiv(@term,...,@term)` predicate,
all the bi-terms that need to be proved equivalent are displayed as a
numbered list.

.. example:: Initial judgment for observational equivalence

   Consider a goal for observational equivalence, where the
   frame is enriched with some public key, as follows:

   .. squirreldoc::

      global goal [myProtocol] obs_equiv t : [happens(t)] -> equiv(frame@t, pk(sk))

   When starting its proof, after doing :g:`intro H`, the goal is
   displayed as:

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

Tactics that apply to judgement whose goal is an equivalence may take a natural number
as argument to identify one item in the equivalence. This is represented
using the :token:`position` token.

.. prodn::
  position ::= @natural

Many tactics expecting a term support term :gdef:`patterns<pattern>`,
which are underspecified term that can includ term holes
:g:`_`. Often-times, the tactic will match the pattern against
sub-terms of the goal until it manages to infer values for the term
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
`book-keeping <https://coq.inria.fr/refman/proof-engine/ssreflect-proof-language.html#bookkeeping>`_,
which are used in Squirrel with a SSReflect inspired syntax.
A more comprehensive and detailed guide to introduction patterns, see
`here <https://coq.inria.fr/refman/proof-engine/ssreflect-proof-language.html#introduction-in-the-context>`_.
Note however that Squirrel supports only a sub-set of SSReflect intro
patterns, and that their behavior in Squirrel may vary in small ways.

Introduction patterns take a different meaning depending
on the tactic in which they are used
(:tacn:`intro`, :tacn:`have`, :tacn:`destruct`, ...). Nonetheless,
a introduction pattern always applies to a set of
focused sub-goals (sometimes taken in a sequent, with a full
proof-context) which they modify. A introduction pattern may create or
close sub-goals. Most introduction pattern act only on the top-most
variables or assumptions of the goal (e.g. if the goal is `x => G` or `H =>
G` then the pattern will start by acting on `x` or `H`).

.. prodn::
   naming_ip ::= {| _ | ? | @idend }
   and_or_ip ::= {| [] | [ {+ @simpl_ip } ] | [{+| @simpl_ip } }]
   simpl_ip ::= {| @naming_pat | @and_or_ip | @rewrite_ip }
   s_item ::= {| // | /= | //= }
   rewrite_ip ::= {| -> | <- }
   expand_ip ::= @/{| @macro_id | @operator_id }
   clear_switch ::= %{ {+ @hypothesis_id} %}
   intro_pat ::= @simpl_ip | @s_item | @expand_ip | @clear_switch | * | >
  
A :gdef:`naming introduction pattern<naming ip>` :n:`@naming_ip` pop
the top-most variable or assumption of the goal and name it according
to the pattern:

* :n:`@ident`: using the name :n:`@ident` provided, which fails if
  :n:`@ident` is already in use;
* :n:`?`: using a name automatically choosen by Squirrel;
* :n:`_`: using an automatically choosen name for variables, and the
  name :n:`_` for assumptions, which is a special name that can never
  by referred to by the user. Note that, contrary to other
  :n:`@hypothesis_id`, several assumption may be named :n:`_`.

A :gdef:`and/or introduction pattern<and or ip>` :n:`@and_or_ip` will,
for each focused sub-goals, destruct the top assumption of the goal:

* :n:`[ @simpl_ip ... @simpl_ip ]`: the top assumption of the goal must
  be a conjunction with as many conjunct as provided simple
  patterns. Destruct the conjunction, handling each conjunct according
  to the corresponding :n:`@simpl_ip`.

* :n:`[ @simpl_ip | ... | @simpl_ip ]`: the top assumption of the goal
  must be a disjunction with as many disjunct as provided simple
  patterns. Destruct the disjunction, creating one new sub-goal for
  each disjunct and handling each of them according to the
  corresponding :n:`@simpl_ip`.

A :gdef:`simplification items<simplification item>` :n:`@s_item`
simplifies the goals in focus of the pattern:

* :g:`//` applies :g:`try auto` to the focused goals;
* :g:`/=` applies :tacn:`simpl` to the focused goals;
* :g:`//=` is syntactic equivalent to :g:`// /=`;

A :gdef:`rewrite ip item<rewrite ip item>` :n:`@rewrite_ip` uses the top assumption to rewrite
the focused goals. The top assumption is cleared after rewriting. 

* :g:`->` reads the top assumption as a left-to-right rewrite rule
* :g:`<-` reads the top assumption as a right-to-left rewrite rule

An :gdef:`expansion item<expansion item>` :n:`@expand_ip` expands definitions in the focused goals:

* :n:`@/@macro_id` expands the applications of the macro symbol
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
hypothesis, axioms or proven goals, in order to derive new facts.

.. prodn::
   proof_term ::= @ident {* @pt_arg}
   pt_arg ::= @sterm_pat | @ident | (% @proof_term) | _

In a :n:`@proof_term` or a :n:`@pt_arg`, an identifier :n:`@ident` must
refer to an hypothesis in the current proof context, an axiom or a
previously proven goal.

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

* Then, this local or global formula :g:`F` is successively modified
  by applying it the the arguments :n:`@pt_arg__1 ... @pt_arg__n`, in
  order, as follows:

  + :n:`@sterm_pat`: the top-most element of
    :n:`F` must be a variable, which is then substituted by :n:`@sterm_pat`,
    e.g. :n:`forall x, F0` is replaced by :n:`(F0{x -> @sterm})`. 
    Moreover, a new term unification variable is created for
    each hole :n:`_` in :n:`@sterm_pat`.

  + :n:`@ident`: the top-most element of :n:`F`
    must be an assumption, which is popped and unified with the formula
    corresponding to the hypothesis, axiom or proven goal identified
    by :n:`@ident`.

  + :n:`(% @proof_term)`: the proof-term argument
    :n:`@proof_term` is (recursively resolved) intro a formula, which is
    then unified with the top-most element of :n:`F`.

  + :n:`_`: if :n:`F`'s top-most element is a variable
    then a new unification variable is created and applied to :n:`F`.
    If :n:`F`'s top-most element is an assumption :n:`H`, a new sub-goal
    requiring to prove :n:`H` is created and discharged to the user.

* Finally, depending on which tactic uses the proof-term, Squirrel
  checks that the term unification variables can all be inferred,
  generalizes the term unification variables that remains, or leave
  the term unification environment unclosed.

.. todo::
   Charlie: need example

  

In practice, the application of a proof-term argument is more complex
that described above, for several reasons:

* checks must be perfomed to ensure that the systems formulas apply-to
  can be made compatible, e.g. apply an axiom over system :g:`[any]`
  to a formula applying over system :g:`[default]` is valid, but the
  converse is not;

* some formula manipulation occurs when trying to mix global and local
  formulas, e.g. when applying a global formula to a local formula.


.. _reduction:

Reduction
---------

Several tactics (e.g., :tacn:`simpl` and :tacn:`auto`) rely on an
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
  - :g:`delta`: replace macros and operators by their definitions;
  - :g:`constr`: automatically simplify trace formulas using
    constraint reasoning.

The :g:`constr` transformation replaces trace (sub-)formulas that
are provably equal to :g:`true` or :g:`false` by this value.
When doing so, the constraint solver takes into account
the current hypotheses but also the conditionals that surround
the trace formula.

The user-defined rewriting transformation eagerly applies the rewrite
rules added to the rewriting database using the :cmd:`hint rewrite`
command.


Automatic simplifications tactics
---------------------------------

There are three automated tactics. The :tacn:`autosimpl` tactic is
called automatically after each tactic, unless the tactical
:tacn:`nosimpl` is used.
     
     
.. tacn:: auto {? @simpl_flags}

     Attempt to automatically prove a goal using the hypothesis.

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

    When the conclusion of the goal is a conjuction, it splits this
    goal into several sub-goals, automatically closing only the trivial
    goals closed by :tacn:`true` and :tacn:`assump`.

    When the conclusion of the goal is a global formula which only contains
    a local formula, the goal is then turned into a local formula. Otherwise
    this does nothing.
    
    Additionaly If the :term:`option` :g:`autoIntro` is set to true, introductions
    are also made automically.



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
     from the equivalence, or replace an item :g:`<u,v>` by :g:`u`
     if it determines that :g:`v` is deducible.

         
.. _section-tacticals:

Tacticals
---------

The full syntax of tactic combinations is as follows:

.. prodn::
   tactical ::=  @tactical; {*, @natural } @tactical
   | @tactical + @tactical
   | by @tactical   
   | nosimpl @tactical
   | try @tactical
   | repeat @tactical
   | @tactical => {+ @intro_pat}
   
The semi-column :g:`;` is used for judgemential composition. The second tactical is then applied to all sub-goals created by the first one, unless number of sub-goals are specified. The :g:`+` performs a or-else when the first tactical fails.

The reminder behaves as follows:

.. tacn:: by @tactical
    
   Fails unless the tactical closes the goal.

.. tacn:: nosimpl @tactical

  Call tactic without the subjudgement implicit use of simplications.
  This can be useful to understand what's going on step by step.
  This is also necessary in rare occasions where simplifications are
  actually undesirable to complete the proof.

.. tacn:: try @tactical

  Try to apply the given tactic. If it fails, succeed with the
  sub-goal left unchanged.

.. tacn:: repeat @tactical

  Apply the given tactic, and recursively apply it again on the
  generated sub-goals, until it fails.

.. tacn:: @tactical => @intro_pat_list

   .. prodn:: intro_pat_list ::= {* @intro_pat}

   :n:`@tactical => @intro_pat_list` is equivalent to :n:`@tactical; intro @intro_pat_list`
  
Common errors
-------------

.. exn:: Out of range position.

   Argument does not correspond to a valid equivalence item.

.. exn:: Assumption not over valid system

   Trying to use a proof term that does not apply to the current system.
   

Tactics
=======

Tactics are organized in three categories:

 - :ref:`generique <section-generic-tactics>`, that rely on generic logical reasoning;
 - :ref:`structural <section-structural-tactics>`, that rely on properties of protocols and equality;
 - :ref:`cryptographic <section-crypto-tactics>`, that rely on some
   cryptographic assumptions.

In addition, they are also split between tactics applicable to
:term:`local goals <local goal>` only, :term:`global goals <global
goal>` only, or tactics common to both types of goals. Remark that
applying a tactic to a local goal may produce a global sub-goal, and
conversely.

Additionaly, we also have a few :ref:`utility tactics <section-utility-tactics>` listed at the end.

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
      
    Concludes if the goal or false appears in the hypotheses. The
    hypothesis to be checked against may be directly specified using
    :n:`@hypothesis_id`.


.. tacn:: case {| @hypothesis_id | @term_pat}
    
   Perform a case analysis over the given argument:
   
   - :n:`@hypothesis_id`: create on sub-goal for each disjunct of
     :n:`@hypothesis_id`;
   - :n:`@term_pat` a term of type :g:`timestamp`: create one sub-goal
     for each possible :term:`action constructor<action constructor>` of the sequent current
     system
     (all systems appearing in a sequent have the same set of actions,
     as they must be be compatible).
      

.. tacn:: induction {? @term_pat}

   Apply the induction scheme to the conclusion. There are
   several behaviours depending on the current type of the goal
   and whether an argument given.

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
      performed over this variable as well as a case over all
      possible actions;
    - for any other term argument, the
      tactic behave as in the reachability case.

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

       Calling :g:`induction t` will behave in apply the weak
       induction and case, yielding as many goals as there are actions
       in the protocol, plus one additional goal for the
       initialization. Assuming an action :g:`A` is in the protocol,
       that has a total of 3 actions, a corresponding created subgoal
       will look like

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

    This always behaves as the induction in the reachability goal
    setting (also for equivalence goals),
  
.. tacn:: destruct @hypothesis_id {? as @simpl_ip}
    
    Destruct an hypothesis based on its top-most connective
    (existantial quantification, disjunction or conjunction), 
    applying the simple introduction pattern :n:`@simpl_ip` to it.

    :n:`@simpl_ip` defaults to :n:`?` if not pattern is provided by the user.
    
    .. example:: Destruct 
       
       If we have the hypothesis :g:`H: A \/ (B /\ C)`, the tactic

       .. squirreldoc::
       
          destruct H as [H1 | [H2 H3]]
          

       removes the :g:`H` hypothesis and create two sub-goal, one with the hypothesis :g:`H1:A`, the other
       with the hypotheses :g:`H2:B, H3:C`.
    
.. tacn:: exists {* @term}
    
    :n:`exists @term__1 ... @term__n` uses the terms :n:`@term__1 ... @term__n` 
    as witnesses to prove an existentially quantified goal.

    For example, :g:`exists t` transform a goal
    :n:`(exists x, phi)` into :n:`(phi{x -> t})`.
    
.. tacn:: generalize {+ @term_pat} {? as {+ @variable}}
   :name: generalize    

    :n:`generalize @term_pat` looks for an instance :n:`@term` of
    :n:`@term_pat` in the goal. Then, replace all occurrences of :n:`@term`
    by a fresh universally quantified variable
    (automatically named, or :n:`@variable` if provided).

.. tacn:: generalize dependent {+ @term_pat} {? as {+ @variable}}
   :name: generalize dependent
    
    Same as :n:`generalize`, but also generalize in the proof context.
    All hypotheses in which generalization occured are pushed back into the
    goal before the newly added quantified variables.

.. tacn:: have @have_ip : {|@term|@global_formula}
   
   .. prodn:: have_ip ::= {* @s_item} @simpl_ip {* @s_item}

   :n:`have @have_ip : F` introduces the new hypothesis :n:`F`, which
   can be a :n:`@term` or a :n:`@global_formula`. The new
   hypothesis is processed by :n:`@have_ip` (see below). A new
   sub-goal requiring to prove :n:`F` is created.

   If :n:`@have_ip` is the introduction pattern :n:`@s_item__pre @simpl_ip @s_item__post` then:

   * the simplification item :n:`@s_item__pre` is applied to the *goal*
     before adding the hypothesis;

   * the simple intro-pattern :n:`@simpl_ip` is applied to introduce the
     *new hypothesis* :n:`F`;

   * the simplification item :n:`@s_item__post` is applied to the *goals*
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
   enviroment is closed --- and process the resulting formula using introduction
   pattern :n:`@have_ip`.
        
.. tacn:: apply @proof_term
   :name: apply 
    
   Backward reasoning tactic.
   First, :n:`@proof_term` is :ref:`resolved <section-pt-resolution>` as a
   formula :n:`F__pt`
   --- without closing the term unification enviroment. 
   Then, unify it with the goal, and finally closes the term
   unification environment.

   If the unification of :n:`F__pt` with the goal fails, introduces
   the top-most element of :n:`F__pt` as described below and then try again to unify with
   the goal:
   
   * if it is a variable (i.e. :n:`F__pt = forall x, F`), introduces a new term
     unification variable :n:`x` and continue from :n:`F`;

   * if it is an assumption (i.e. :n:`F__pt = G => F`), discharge the
     assumption :n:`G` as a new sub-goal and continue from :n:`F`.

.. tacn:: apply @proof_term in @hypothesis_id

   Forward reasoning variant of :tacn:`apply`, which unifies the
   premisses of :n:`@proof_term` against the conclusion of
   :n:`@hypothesis_id`, replacing :n:`@hypothesis_id` content by
   :n:`@proof_term` conclusion.

   E.g., if :n:`H1:A=>B` and :n:`H2:A` then :g:`apply H1 in H2` replaces
   :n:`H2:A` by :n:`H2:B`. 

.. tacn:: rewrite {* @rw_arg} {? in @rw_target}
    
   .. prodn:: rw_arg ::= {| @s_item | @rw_item }
               rw_item ::= {? {| {? @natural} ! | ?}} {? <-} {| (@proof_term) | /@ident | /( @infix_op) | /*}
               rw_target ::= {| @hypothesis_id | *}
       
   Applies a sequence of :term:`rewriting <rewrite ip item>` and :term:`simplification
   <simplification item>` items to the rewrite target, which is:
    
   * the hypothesis :n:`@hypothesis_id` if :n:`rw_target = @hypothesis_id`;
   * all hypotheses if :n:`rw_target = @hypothesis_id`;
   * the goal if no specific rewrite target is given.

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
       matched instance of :n:`l` are replaced by the corresponding
       instantiation of :n:`r`.
      
     + The term unification environment is closed, and new sub-goals are created 
       for the instantiated assumptions :n:`H1,...,Hn`.

   * expansion items :n:`/@ident` and :n:`/( @infix_op)`: try to expand the corresponding
     symbol (see :term:`expansion item`), while :n:`/*` tries to
     expand all possible symbols;

   * :n:`!` apply the rewrite item as many times as possible, but at least once,
     while :n:`(@natural !)` apply the rewrite item exactly :n:`@natural` times.
     :n:`?` behaves as :n:`!`, except that the rewrite item may be applied zero times.
     Otherwise, the rewrite item must be applied exactly once.

   .. exn:: rule bad systems
   
      Rewrite item applies to a system which is not compatible with the rewrite target.
    
   .. exn:: nothing to rewrite
   
      No instance of the rewrite rule were found
    
   .. exn:: maxed nested rewriting
    
      There were too many nested rewriting. This is to avoid infinite rewriting loops.

.. tacn:: id

   The identity tactic, which does nothing. Sometimes useful when
   writing :ref:`tacticals<section-tacticals>`.
    

.. tacn:: intro {+ @intro_pat}
    
    Introduce the top-most variables and assumptions of the goal as
    specified by the given introduction patterns.

.. tacn:: clear {* @hypothesis_id}
    
    Drop the specified hypotheses. 

.. tacn:: reduce {? @simpl_flags}

     Reduce all terms in a sub-goal, working on both hypotheses and conclusion.
     
     This tactic always succeeds, replacing the initial sub-goal with a
     unique sub-goal (which may be identical to the initial one).

     The tactic uses the :ref:`reduction engine <reduction>`
     with the provided flags (defaults to :g:`rw,beta,proj`).
     
.. tacn:: remember @term_pat

    :tacn:`remember` behaves as :tacn:`generalize`, except that it adds
    as an hypothesis the equality between the generalized term and the
    new variable.
      
       
.. tacn:: revert {* @hypothesis_id}
    
    Remove the hypotheses from the proof context, and add them back
    into the goal.

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
    For example, :tacn:`split` replace the goal :n:`⊢ F && G && H`
    by the three goals :n:`⊢ F`, :n:`⊢ G` and :n:`⊢ H`.
       
.. tacn:: use @hypothesis_id {? with {+ @term}} {? as @simpl_ip}
   :name: use     
    
   Instantiate a lemma or hypothesis using the provided arguments (if
   any). An introduction pattern can also be specified to handle the
   new hypothesis.

   .. warning::
      This tactics is a deprecated (and less powerful) variant of the
      :tacn:`have` tactic (with the :n:`have @have_ip := @proof_term`
      form).
      
Local tactics
~~~~~~~~~~~~~

.. tact:: true
   :name: true    
    
   Closes a goal when the conclusion is true. 

      
Global tactics
~~~~~~~~~~~~~~

.. tace:: byequiv
    
   Transform an global judgement :n:`⊢ [F]` into a local judgement
   :n:`⊢ F`.

.. tace:: constseq @position: {+ (fun @binders => @term) @term}

   Simplifies a sequence at the given :n:`@position` when it only
   contains a finite number of possible values :g:`v_1`,..., :g:`v_i`
   depending on the value of the sequence variable.

   Given a sequence over a variable of a given type, the arguments
   passed must be of the form :g:`(fun_1 v_1) ... (fun_i v_i)`, where
   all the :g:`fun` function must be binders over the sequence type
   and must return a boolean.  This tactic creates two sub-goals
   asking to prove the two required properties of the arguments and
   sequence:

   * All the functions must be such that over an input element one
     and only one of the function return true.
   * The sequence is then expected to be equal to the value of `v_i`
     for all input elements such that fun_i is true.

   .. example::  Constseq one or zero

      Consider the following conclusion goal :g:`0:
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
    
    Enrich the equivalence goal with the given terms.
    Note that this changes the number of items in the equivalence, and
    if added before other tactics may break later references.

.. tacn:: localize @hypothesis as @simpl_ip
    
    Change a global hypothesis containing a reachability formula
    :n:`[@term]` to a local hypothesis :n:`@term`, and applies the
    given simple introduction pattern :n:`@simpl_ip` to the new hypothesis.

    For example, turns :n:`[F],G ⊢ H` into :n:`F,G ⊢ H`.
       
.. tace:: memseq
    
    Prove that a bi-frame element appears in a sequence of the bi-frame. 

    .. todo::
       Charlie: hum. There are no examples nor test for this function.
       It should be tested before being documented (don't know who did it)
       

.. tace:: refl
    
    Closes a symmetric goal. Cannot apply if the goal contains
    variable or macros, as those may have different left and right
    behaviors.

.. tace:: sym
    
    Swap the left and right system of the equivalence goal.

.. tace:: trans
    
    Prove an equivalence by transitivity.

    .. todo::
       Adrien: this deserves an explanation, the tactic actually does a lot.

.. tace:: splitseq @position: (fun @binders => @term)
    
   Splits a sequence according to some boolean test, replacing the
   sequence by two subsequence.

   The function passed as argument must be a function taking as
   argument a variable of the same type as the sequence and must
   return a boolean.

   .. example:: Splitting a sequence
      
      Called over a conclusion of the form :g:`0: seq(x:message =>
      value)`, the tactic:

      .. squirreldoc::

         splitseq 0: (fun y:message => some_test)

      replaces the conclusion by:

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
     after the destruction of conjunctions (but no case analyses are
     performed to handle conjunctive hypotheses). If the conclusion
     is a trace literal then it is taken into account as well.

    
.. tacn:: depends @timestamp, @timestamp
    
    If the second action depends on the first action, and if the second
    action happened, add the corresponding timestamp
    inequality.

    .. exn:: Not dependent

       The two actions are not dependent, i.e. were not derived
       from two outputs in sequence in the source process.

.. tacn:: expand {+, @macro_id | @macro_application }
    
    Expand all occurences of the given macros in both the goal and the
    proof context, either fully specified with an action or simply a type
    of macro.
    
.. tacn:: expandall
    
    Expand all possible macros in the judgement. 
             

.. tacn:: fa {|@position | {+, @fa_arg}}
   :name: fa
    
   .. prodn::
      fa_arg ::= {? {| ! | ?}} @term_pat

   Applying the function application rule, simplifying the goal by
   removing the head function symbol, as follows:
   
   * in a local goal with conclusion :g:`f u = f v`, the conclusion is
     replaced with :g:`u=v`. This produces as many subgoals as argument
     of the head function symbol. For a local goal, the tactic takes no
     arguments.
   * in a global goal, replace :g:`f(u1,...,un)` with :g:`u1,...,un`.

     
   In the global goal setting, the target can be selected with its
   :n:`@position`, or using a :n:`@fa_arg`, which behave as follow:

   * :g:`fa` :n:`@term_pat` selection the first position in the equivalence
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
   and global, after the destruction of conjunctions (but no case analyses 
   are performed to handle conjunctive hypotheses). If the conclusion
   is a message (dis)-equality then it is taken into account as well.

.. tact:: const @variable
    
   Add the `const` tag to a variable.

   The variable must be of a finite and fixed (η-independent) type,
   and must not appear in any global hypothesis (some global
   hypotheses may be localized (see :tacn:`localize`) if necessary.

      
.. tact:: eqnames
    
    Add index constraints resulting from names equalities,
    modulo the known equalities.
     
    If :g:`n[i] = n[j]` then :g:`i = j`. This is checked on all name
    equality entailed by the current context.

.. tact:: eqtrace
    
    Add terms constraints resulting from timestamp and index
    equalities. 

    Whenver :g:`i=j` or :g:`ts=ts'`, we can substitute one by another
    in the other terms.

.. tact:: executable @term
    
    Assert that :g:`exec@_` implies :g:`exec@_` for all previous
    timestamps. 

    Given as input a timestamp :g:`ts`, this tactic produces two new
    sub-goal, requiring to prove that :g:`happens(ts)` holds and that
    :g:`exec@ts` also holds. The fact that :g:`(forall (t:timestamp),
    t <= ts => exec@t)` is added to the current goal.


.. tact:: project
    
    Turn a local goal on a :term:`multi system` into one goal for each
    single system in the multi-system.

.. tact:: rewrite equiv {? -}@proof_term
    
    Use an equivalence to rewrite a reachability goal.

    First, try to resolve :n:`@proof_term` as an equivalence
    :g:`equiv (diff(u,v))`. Then, Squirrel tries to find a context :g:`C`
    that does not contain any :decl:`names<name>`, :term:`diff-terms<diff-term>`
    or :term:`macro terms<macro>` such that the current local goal :g:`phi` is
    convertible with :g:`C[u]`. If such a context is found, the current goal is
    is changed to :g:`C[v]`.

    If a :g:`-` sign is added in front of :n:`@proof_term`, the
    rewriting occurs in the other direction, replacing :g:`v` by
    :g:`u`.

    .. example:: Hash rewrite

       Consider the following judgment

       .. squirreldoc::
          [goal> Focused goal (1/1):
          System: default/left (equivalences: left:default/left, right:default/right)
          H: equiv(diff(h (a, k), n), diff(h (b, k), m))
          U: [a <> b]
          ----------------------------------------
          h (a, k) <> h (b, k)

       Assuming we have been able to prove that two hashes are
       indistinguishable from names, we have hypothesis :g:`H`. We
       then use :g:`H` to replace the hashes by names in our current
       goal, where we want to prove that the two hashes are not equal.

       Calling :g:`rewrite equiv H` produces the new goal:
       
       .. squirreldoc::
          [goal> Focused goal (1/1):
          System: default/right (equivalences: left:default/left, right:default/right)
          H: equiv(diff(h (a, k), n), diff(h (b, k), m))
          U: [a <> b]
          ----------------------------------------
          n <> m

.. tact:: slowsmt
    
    Version of the :tacn:`smt` tactic with higher time limit. 
      
.. tact:: smt
   :name: smt    
    
    Tries to discharge the current goal using an SMT solver. 
      

.. tact:: subst @term, @term

    If :g:`x = t` where :g:`x` is a variable, then :g:`subst x, t`
    substitutes all occurences of :g:`x` by :g:`t` and remove :g:`x`
    from the :term:`logical variables <logical_var>`.

    .. exn:: Unequal arguments

       Terms given as arrgument are not equal.
       
    
    
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

    This rely on some heuristical automated reasoning. Some properties on
    macros are automatically exploited, e.g. that for any
    timestamp :g:`t`, :g:`frame@pred(t)` allows to deduce
    :g:`input@t`, all :g:`frame@t'` for :g:`t' < pred(t)`, as well as
    the :g:`output@t'` for whenever :g:`exec@t'` is true.

    .. todo::
       Charlie: do we want an exhaustive description of the deduce algo?
       
       Adrien: without arguments, it removes all elements that can be
       dropped I think.

.. tace:: diffeq
    
   Closes a reflexive goal up to equality. That is, if all diff-term
   whitin the global goal always evaluate to the same value in all
   systems, the diff-equivalence holds. For each diff-term, a
   dedicated sub-goal is created.
      
   .. warning:: This tactic is still at an experimental development
       stage. We do not recommend its usage.     

.. _section-crypto-tactics:

Cryptographic tactics
---------------------

Cryptographic tactics enables reasoning over cryptographic and
probabilistic properties of random samplings and primitives.

Occurrence formula
~~~~~~~~~~~~~~~~~~

Several reasonings imply to be able to track how a given name is
used. For instance, if the name :g:`n` does not ocurr at all in term
:g:`t`, then :g:`n=t` is false with overwelming probability. To apply
a cryptographic assumption that needs a secret key, one need to check
that all occurrences of the secret key are valid ones, e.g. only used
in key position of the corresponding primitive.

Over macro-free terms, collecting occurrences is simply equivalent to
looking at the subterms. However, if some macros occur in :g:`t`,
typically :g:`input@ts` or :g:`output@ts`, we need to look through all
the actions that may have happened before :g:`ts` and may depend on
:g:`n`.

We define here how to build an :gdef:`occurrence formula` that will be
reused in several tactics description. For any name :g:`n`, any term
:g:`t` and a set of allowed patterns :g:`pats` (patterns built over
the name :g:`n` and function applications), we define the formula
:g:`occurs(n,t,pats)` as the conjunction of conditions under which it
is possible that :g:`n` occurs in :g:`t` without following one of the
allowed pattern of `pats`:

* whenever :g:`t` contains as a subterm an occurrence :g:`n` that does
  not follow any of the allowed patterns :g:`pats`, the formula is
  :g:`true`.
* whenever :g:`t` contains a :ref:`system-defined
  macro<section-system-macros>`, :g:`macro@ts`, if `ts` is a concrete
  action, we simply unfold the definition of the macro, and whenever
  is it not concrete, we collect all actions of the form :g:`A1` such
  that :g:`n` occurs in the definition of the action not as an allowed
  pattern, and the formula :g:`A1<=ts` is added to the conjunction of
  :g:`occurs(n,t,pats)`.

Occurs is of course generally defined for indiced names that may
occured in index actions.

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
more precisly the usages of the states, and also adds the condition
that the correct value of the state is revealed if a state can contain
an occurrence of :g:`n`.

We also generalize occur to allow for collecting multiple name
occurrences at once, useful when we want to allow patterns depending on
two names at once (see e.g. :tacn:`gdh` or :tacn:`ddh`).

.. todo::
   Adrien: how name occurrences are computed is quite complicated, and
   more involved than what is described here I think (conditions,
   source terms, occurrences below bound variables, fold-macro-support
   shenanigans, ...)

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
   
   In a local goal, called over an hypothesis of the form :g:`t=n` for
   some name :g:`n` over a current goal formula :g:`phi`, turns the
   goal into a formula :g:`occur(n,t,none) => phi` (see the
   definition of the :term:`occurrence formula`).

   If one can then prove that :g:`n` cannot occur in :g:`t`, that is
   that :g:`occur(n,t,none)` is false, it then allows to close
   the goal. If :g:`occur(n,t,none)` is trivially false, e.g. if
   :g:`t` is a macro-free term without :g:`n` as a subterm, the goal
   will be directly closed.


   .. example:: Name leak

      Consider a small process :g:`in(c,x); A : out(c,x);in(c,x); B:
      out(c,n)`, where we want to prove that :g:`input@A <>
      n`. Intuitively, this holds as :g:`n` is only revealed after
      :g:`A` has occured.

      The judgment corresponding to this proof will look like this:

      .. squirreldoc::
         [goal> Focused goal (1/1):
         System: left:default/left, right:default/right
         Eq: input@A = n
         H: happens(A)
         ----------------------------------------
         false

      And calling :g:`fresh Eq` turns the judgment into:

      .. squirreldoc::
         [goal> Focused goal (1/1):
         System: left:default/left, right:default/right
         Eq: input@A = n
         H: happens(A)
         ----------------------------------------
         B < A => false

      Here, Squirrel automatically deduced that :g:`n` can only occur
      inside :g:`input@A` if the output of :g:`B` happened before
      :g:`A`. Here, one would conclude by using the fact that in the
      process definition, this is impossible.
      
   In an equivalence goal, the tactic must be applied to a bi-frame
   element :g:`i` of the form :g:`diff(nL,nR)`.  If we denote by
   :g:`bf` the bi-frame, the bi-frame element is then replaced by

   .. squirreldoc::
      if not(diff(occur(nL,bf,i : diff(nL,nR)),occur(nR,bf,i : diff(nL,nR)))) then
        zero
      else
        diff(nL,nR)

   We specify through the occur formula that the only possible
   occurrence of nL is in fact the one we are currently looking at.

   In all cases, the :g:`precise_ts` makes the tactic use
   `precise_occur` instead of `occur`.

   Latest formal Squirrel description: :cite:`bkl23hal` (Appendix F).

Local tactics
~~~~~~~~~~~~~


.. tact:: cdh @hypothesis_id, @term
   :name: cdh

   This tactic applies the Computational Diffie-Helman assumption (see
   e.g. :cite:`okamoto2001gap`), stating that given two groups elents
   :math:`g^a` and :math:`g^b` it is difficult to compute :math:`g^{ab}`.

   A cdh, ddh or gdh :term:`group declaration <group declaration>` must have been
   specified. For a group with generator :g:`g` and exponentiation
   :g:`^`, calling :g:`cdh M, g` over a message equality :g:`M` of the
   form `t=g^{a b}` will replace the current goal :g:`phi` by
   :g:`occur(a,t,g^a) || occur(b,t,g^b) => phi` (see the
   definition of the :term:`occurrence formula`). If :g:`a`
   and :g:`b` only occur as :g:`g^a` and :g:`g^b`, the goal is then
   closed automatically.
    
   .. warning::
      This is a work in progress, a formal description of the rule is pending.

   .. todo::
      why is it WIP?
            
.. tact:: collision
   :name: collision
    
   Requires a :term:`hash function declaration <hash function>`.

   This tactis applies the known key collision resistance assumption
   (see e.g. the cr2-kk assumption from
   :cite:`goldwasser1996lecture`).
    
   Collects all equalities between hashes occurring at toplevel in
   message hypotheses, that is all hypothesis of the form
   :g:`h(u,k)=h(v,k)`, and for each such hypothesis it adds as new
   hypothesis :g:`u=v`.

   As this supports the known-key variant of collision resistance,
   there is no side condition checked here over the hash key.

   Latest formal Squirrel description: :cite:`bkl23hal` (only as an example).       

.. tact:: euf @hypothesis_id
   :name: euf
    
   Requires either a :term:`hash function` or a :term:`signature
   scheme` declaration.

   This tactic applies the UF-CMA axiom, either for keyed-hashes or
   signatures. (see e.g. :cite:`goldwasser1996lecture`)

   For a hash function :g:`h(x,k)`, one may call :g:`euf M` over a
   message equality :g:`M` of the form :g:`t = h(m,k)` or
   :g:`h(m,k)=t`.  The tactic then create a first new subgoal asking
   to prove that the key is only used in correct position, that is a
   goal with conclusion :g:`not(occur(k,goal,h(_,k))` (see the
   definition of the :term:`occurrence formula`).  The tactics then
   collects all possible occurrence of honest hash :g:`h(u,k)` inside
   :g:`t`, and for each of them, creates a subgoal with a new
   hypothesis stating that :g:`m=u`. If such an occurrence happens
   under a macro, the goal will state that the computation must have
   happened before.

   .. example:: Basic hashing
    
      Consider the following system:
      
      .. squirreldoc::
         hash h
         name k:message
         channel c
         name n : message
         name m : message
      
         system (!_i out(c,h(n,k)) | in(c,x);out(c,x)).

      Calling :g:`euf` over an hypothesis of the form :g:`input@tau <>
      h(m,k)` would add n the fact that :g:`h(m,k)` needs to be equal
      to one of the honestly computed hashes appearing in
      :g:`input@tau`, which are all of the form :g:`h(n,k)`. The new
      hypothesis would then be equal to

      .. squirreldoc::
        (exists (i:index), A(i) < tau && m = n)
   
   For a signature function :g:`sign(x,r,k)`, public key :g:`pk(k)`
   and check function :g:`check(s,m,pub)`, :g:`euf` must be called
   over an hypothesis of the form :g:`check(s,m,pk(k))`. The behaviour
   is then similar to the hash case, honest signatures that may occur
   in s will be collected, and :g:`m` must be equal to one of the
   honestly signed message. A subgoal for each possible honest signing
   case is created, as well as a subgoal specifying that the key is
   correctly used, that is, a goal with conclusion
   :g:`not(occur(k,goal,sign(_,k), pk(k))`.
    
   Latest formal Squirrel description: :cite:`bkl23hal`.
       
.. tact:: gdh @hypothesis_id, @term
   :name: gdh

   This tactic applies the gap Diffie-Hellman assumption (see
   e.g. :cite:`okamoto2001gap`), which is similar to CDH over :g:`g^a`
   and :g:`g^b` but the attacker is also allowed to access an oracle
   testing equality to :g:`g^ab`. It also includes the square GDH
   variant (see :cite:`fujioka2011designing`), equivalent to the GDH
   assumption for prime order groups, where the attacker can also test
   equality to :g:`g^aa` and :g:`g^bb`.

   A gdh :term:`group declaration <group declaration>` must have been
   specified.

   The behaviour of the tactic is similar to :tacn:`cdh`, expect that
   the current goal :g:`phi` is replaced by a more permissive formula
   :g:`occur((a,b),t,(g^a,g^b,_=g^(ab), _=g^(bb), _=g^(aa)) => phi`
   (see the definition of the :term:`occurrence formula`).

   .. warning::
      This is a work in progress, a formal description of the rule is pending.       

.. tact:: intctxt @hypothesis_id
   :name: intctxt
    
   This tactics applies the INT-CTXT assumption (see
   e.g. :cite:`bellare2000authenticated`).

   It requires the declaration of a :term:`symmetric encryption`.
   
   It can be applied to an hypothesis either of the form
   :g:`dec(c,k)<>fail` or :g:`dec(c,k) = t` (in the latter case,
   generates as an additional goal that `t <> fail`).

   In both cases, Squirrel will collect all honest encryptions made
   with key :g:`k`, and produce a subogal corresponding to each case
   where :g:`c` is equal to one of those honest encryptions.

   The key :g:`k` must only be used in key position, so a subgoal
   asking to prove that :g:`not(occur(k,c,(enc(_,_,k),dec(_,k)))` is
   created when it is not trivially true (see the definition of the
   :term:`occurrence formula`).

   In additition, a goal asking to prove that all randomness used for
   encryption are disjoint and fresh (when it is not trivially true).

   Latest formal Squirrel description: :cite:`bdjkm21sp`.      


Global tactics
~~~~~~~~~~~~~~

.. tace:: cca1 @position
   :name: cca1
    
   This tactics applies the IND-CCA assumption (see
   e.g. :cite:`bellare2000authenticated`).

   It requires the declaration of a :term:`symmetric encryption` or
   an :term:`asymmetric encryption`.

   The tactic can be called over a bi-frame element containing a term of
   the form :g:`C[enc(n, r, m)]`, where
        
   • :g:`r` must be a name which is fresh;
   • there is no decryption in :g:`C`
   • there is no universal message variable that occurs
   • :g:`m` is  a key  or a public key such that the key
     only appear in key position, under :g:`pk`, :g:`dec` or
     :g:`enc`.    


   The tactic will then replace the encryption occurrence by an
   encryption of zeroes, yielding :g:`C[enc(zeroes( len(n)), r,
   pk(k))]`.


   In addition, the tactic creates a subgoal asking to prove that all
   occurrences of the key and encryptions are correct. Notably, one
   must prove that :g:`occur(k,bi-frame,(enc(_,_,k), dec(_,k))` (see
   the definition of the :term:`occurrence formula`) is false (or
   :g:`occur(k,bi-frame,(pk(k), dec(_,k))`) for the asymmetric case).

   In addition, in the asymetric case, a subgoal is created to prove the
   freshness of the random used in the encryption, with the conclusion
   :g:`occur(r,bi-frame,enc(n,r,m))`.

   In the symmetric case, an additional subgoal is created ensuring
   that all encryptions are made with distinct fresh randoms (and not
   that just the encryption we are looking at is fresh).

   Latest formal Squirrel description::cite:`bkl23hal`.  
    
.. tace:: ddh @term, @term, @term, @term
   :name: ddh


   This tactic applies the Decisional Diffie-Helman assumption (see
   e.g. :cite:`okamoto2001gap`), stating that given two groups elents
   :g:`g^a` and :g:`g^b` it is difficult to distinguish :g:`g^(ab)`
   from a fresh :g:`g^c`.

   A ddh :term:`group declaration <group declaration>` must have been
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

   The tactic can be called over a bi-frame element containing a term of
   the form :g:`C[enc(n, r, m)]`, where
        
   • :g:`r` must be a name which is fresh;
   • there is no decryption in :g:`C`
   • there is no universal message variable that occurs
   • :g:`m` is either a key or the diff of two keys, such that the
     keys only appear in key position, under :g:`pk`, :g:`dec` or
     :g:`enc`.
   • If :g:`m` is a key, and a key has been given as argument to the
     tactic, this key must also occur only in key position.

   When :g:`m` is the diff of a key, the diff is simplified by keeping
   only the key on the left. When :g:`m` is just a key, a new key by
   which it is replaced can be specified as arugment.
   
   .. example:: Basic ENC-KP application
   
      On a bi-frame element of the form
      
      .. squirreldoc::
         i : enc(n,r,diff(pk(k1),pk(k2)))
   
      calling the tactic :g:`enckp i` will simplify the bi-frame
      element by only keeping the key on the left, yielding
      
      .. squirreldoc::
         i: enc(n,r,pk(k1))

   The tactic expects as argument:
   
   • the number identifying the bi-frame element;
   • optional: the encryption term over which to apply the tactic;
   • optional: the new key by which to replace the key.


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

   When it is not trivially true, a subgoal is created to prove the
   freshness of the random used in the encryption, with the conclusion
   :g:`occur(r,bi-frame,enc(n,r,m))`.

   In the symmetric case, an additional check is performed ensuring
   that all encryptions are made with distinct fresh randoms (and not
   that just the encryption we are looking at is fresh).
   
   Latest formal Squirrel description::cite:`bdjkm21sp`.
      
.. tacn:: prf @position {? , @term_pat}
   :name: prf

   This tactic applies the PRF assumption (see
   .e.g. :cite:`goldwasser1996lecture`).

   It requires a :term:`hash function` declaration.

   This tactic applied to a bi-frame element containg a hash
   application :g:`h(m,k)` tries to replace the hash value by a fresh
   name, under the conditions that it is the first time that this
   specific hash value is hashed and that the key is correctly used.


   Formally, when called over a bi-frame element :g:`i : C[h(m,k)]`,
   the tactic replaces in the current goal the element by :g:`i :
   C[nPRF]` where :g:`nPRF` a newly generated unique name. It in
   additions produces subgoal requiring to prove the side
   conditions. It notably produces a goal asking to prove that the key
   is only used in key position, that is that
   :g:`occur(k,bi-frame,h(_,k))` is false (see the definition of the
   :term:`occurrence formula`). In addition, it creates for each
   occurrences of :g:`h(t,k)` within the bi-frame (that may occur under
   macros) a subgoal asking to prove that :g:`t <> m`, that is, that
   :g:`m` was never hashed before. Such subgoals may need to be
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

      This replaces in the current goal the hash occurrence by
      :g:`diff(n_PRf,p)`, and creates a subgoal asking to prove that
      the hash message :g:`n` is different from any possible
      previously hashed message. Here, the only other possible hash
      would occur in :g:`frame@pred(A)`, in the output of :g:`B` if it
      occured before :g:`A`. The created subgoal then ask to prove
      that :g:`[B < A => n <> m]`.


   If multiple occurrences of hashes occur in the bi-frame element, the
   first one is targeted by default. Calling the tactic with an
   optional :n:`@term_pat` allows to target a specific hash occurrence.

   Latest formal Squirrel description: :cite:`bkl23hal`.
       
.. tace:: xor @position {? , @term_pat} {? , @term_pat}

   This tactic applies the unconditionally sound one time pad property
   of the xor operation.

   The tactic applied to a bi-frame element of the form :g:`i : C[n XOR
   t]` will replace the XOR term by :g:`if occur(n,bi-frame, i : C[n
   XOR t] ) && len(n) = len(t) then n_FRESH else (n XOR t)`. This new
   term then allow to drop the old term only if :g:`n` and :g:`t` do
   have the same length (otherwise the one time pad does not work),
   and if this is the only occurrence of :g:`n` in the bi-frame.

   When multiple XOR occur in the bi-frame, one can specify one or two
   optional term patterns, to specify in any order the name :g:`n` or
   the full xored term :g:`n XOR t` to target.    

   Latest formal Squirrel description: :cite:`bdjkm21sp`.

.. _section-utility-tactics:
  
Utility tactics
---------------


.. tacn:: help {? {|@tacn|concise}}
    
    When used without argument, display all available commands. It can
    also display the details for the given tactic name, or display or
    more concise list. It is a tactic and not a command, it can only
    be used inside proofs.

.. tacn:: lemmas
    
    Print all axioms and proved goals. This is usefull to know which lemmas can
    be used through the :tacn:`use` or :tacn:`apply` tactics.


.. tacn:: prof
    
    Print profiling information. 
      
.. tacn:: show @term_pat
    
    Print the messages given as argument. Can be used to print the values
    matching a pattern. 
      
