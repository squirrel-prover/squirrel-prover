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


When a tactic expect a term (which can then be a local formula), it is allowed to underspecify the term by using holes of the form :g:`_`.

Such term patterns are produced by appending to the production of :n:`@term` and :n:`@sterm` the hole construct:

.. prodn:: term_pat ::= ...
           | _
           sterm_pat ::= ...
           | _

Arguments that are :n:`@term_pat` will first by patterned match against the goal, the match being the actual term passed to the tactics.

Intro patterns
~~~~~~~~~~~~~~
  
Introduction patterns are the principal tool used to do proof-context
`book-keeping <https://coq.inria.fr/refman/proof-engine/ssreflect-proof-language.html#bookkeeping>`_.
Squirrel using a SSReflect inspired syntax.
A more comprehensive and detailed guide to introduction patterns, see
`here <https://coq.inria.fr/refman/proof-engine/ssreflect-proof-language.html#introduction-in-the-context>`_.
Note however that Squirrel supports only a sub-set of SSReflect intro
patterns, and that behavior may vary in small ways.

Introduction patterns behavior depends on the tactic they are being
used in (:tacn:`intro`, :tacn:`have`, :tacn:`destruct`, ...). Nonetheless, 
a introduction pattern always applies to a set of
focused sub-goals (sometimes taken in a sequent, with a full
proof-context) which they modify. A introduction pattern may create or
close sub-goals. Most introduction pattern act only on the top-most
variables or assumptions the goal (i.e. if the goal is `x => G` or `H =>
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

In a :n:`@proof_term` or a :n:`pt_arg`, an identifier :n:`@ident` must
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

  + :n:`_`: if :n:`F` top-most element is a variable
    then a new unification variable is created and applied to :n:`F`.
    If :n:`F` top-most element is an assumption :n:`H`, a new sub-goal
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
     with the provided flags.

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
     with the provided flags.

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


Tactics
=======

Tactics are organized in three categories:

 - :ref:`generique <section-generic-tactics>`, that rely on generic logical reasoning;
 - :ref:`structural <section-structural-tactics>`, that rely on properties of protocols and equality;
 - :ref:`cryptographic <section-crypto-tactics>`, that rely on some
   cryptographic assumptions.

In addition, they are also split between tactics applicable to
:term:`local goals <local goal>` only, :term:`global goals <global
goal>` only, or tactics common to both types of goals. Remark that the
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
   conclusion must be a universal quantification over a
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
        
.. tacn:: id

   The identity tactic, which does nothing. Sometimes useful when
   writing :ref:`tacticals<section-tacticals>`.
	  

.. tacn:: intro {+ @intro_pat}
    
    Introduce the top-most variables and assumptions of the goal as
    specified by the given introduction patterns.

.. tacn:: clear @hypothesis_id
    
    Drop the specified hypothesis. 

.. tacn:: reduce {? @simpl_flags}

     Reduce all terms in a sub-goal, working on both hypotheses and conclusion.
     
     This tactic always succeeds, replacing the initial sub-goal with a
     unique sub-goal (which may be identical to the initial one).

     The tactic uses the :ref:`reduction engine <reduction>`
     with the provided flags.
     
.. tacn:: remember @term_pat
    
    Substitute the given term by a fresh variable and adds as hypothesis the equality between the term and the new variable.
      
       
.. tacn:: revert @hypothesis_id
    
    Remove the hypothesis :n:`@hypothesis_id : H` from the judgement
    goal hypotheses, and add it back to the goal: if the goal's
    conclusion was :n:`conc`, the new goal's conclusion will be :n:`H => conc`.

.. tacn:: left
    
    Reduce a goal with a disjunction conclusion into the goal where the
    conclusion has been replaced with the first disjunct. 

.. tacn:: right
    
    Reduce a goal with a disjunction conclusion into the goal where the
    conclusion has been replaced with the second disjunct. 

.. tacn:: split
    
    Split a conjunction conclusion, creating one sub-goal per
    conjunct. 

       
.. tacn:: use @hypothesis_id {? with {+ variables}} {? as @simpl_ip}
   :name: use     
    
    Instantiate a lemma or hypothesis based on the given. The
    optionnaly given variables are used to instantiate the universally
    quantified variables of the lemma.  
    An introduction pattern can also be specified.
          

      
Local tactics
~~~~~~~~~~~~~

.. tact:: true
   :name: true    
    
   Closes a goal when the conclusion is true. 

      
Global tactics
~~~~~~~~~~~~~~

.. tace:: byequiv
    
   Transform an global goal which is local formula into a
   reachability.
  

.. tace:: constseq @position: {+ (fun @binders => @term) @term}

   Simplifies a sequence at the given :n:`@position` when it only
   contains a finite number of possible values :g:`v_1`,...,:g:`v_i`
   depending on the value of the sequence variable.

   Given a sequence over a variable of a given type, the arguments
   passed must be of the form `(fun_1 v_1) ... (fun_i v_i)`, where
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
    
             
.. tace:: enrich @term
    
    Enrich the equivalence goal with the given term, that can either be of type :g:`message` or :g:`bool`. Note that this changes the number of items in the equivalence, and if added before other tactics may break later references.


.. tacn:: localize @hypothesis as @simpl_ip
    
    Change a global hypothesis containing a reachability formula
    :n:`[@term]` to a local hypothesis :n:`@term`, and applies the
    given simple introduction pattern :n:`@simpl_ip` to the new hypothesis.

.. tace:: memseq
    
    Prove that a biframe element appears in a sequence of the biframe. 

    .. todo::
       Charlie: hum. There are no examples nor test for this function.
       It should be tested before being documented (don't know who did it)
       

.. tace:: refl
    
    Closes a reflexive goal, where all items must be reflexive. Only
    works if the goal does not contain variable or macros, as those
    may have different left and right behavior.


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
            
.. tace:: sym
    
    Swap the left and right system of the equivalence goal.

.. tace:: trans
    
    Prove an equivalence by transitivity. 


.. _section-structural-tactics:

Structural tactics
------------------

Common tactics
~~~~~~~~~~~~~~

      
.. tacn:: apply @proof_term
   :name: apply 
    
   Backward reasoning tactic.
   First, :n:`@proof_term` is :ref:`resolved <section-pt-resolution>` as a formula :n:`F__pt`
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

   E.g., if :g:`H1:A=>B` and :g:`H2:A` then :g:`apply H1 in H2` replaces
   :g:`H2:A` by :g:`H2:B`. 

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

.. tacn:: expand {+, @macro_id | @macro_application }
    
    Expand all occurences of the given macros in both the goal and the
    hypotheses, either fully specified with an action or simply a type
    of macro.
    
.. tacn:: expandall
    
    Expand all possible macros in the judgement. 
             

.. tacn:: fa {|@position | {+ @fa_arg}}
   :name: fa

   .. prodn::
      fa_arg ::= {? {| ! | ?}} @term_pat

   .. todo::
      TODO

.. tacn:: namelength @term, @term
    
    Adds the fact that two names have the same
    length. The two arguments must the indeed be a :decl:`name`.
      
    Usage: namelength m1, m2  


.. tacn:: rewrite {* @rw_arg} {? in @rw_target}
    
   .. prodn:: rw_arg ::= {| @s_item | @rw_item }
               rw_item ::= {? {| ! | ?}} {? <-} {| (@proof_term) | /@ident | /( @infix_op) | /*}
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

   * :n:`!` asks to apply the rewrite item as many times as possible, but at least once.
     :n:`?` behaves as :n:`!`, except that the rewrite item may be applied zero times.
     Otherwise, the rewrite item must be applied exactly once.

   .. exn:: rule bad systems
   
        Rewrite item applies to a system which is not compatible with the rewrite target.
    
   .. exn:: nothing to rewrite
   
        No instance of the rewrite rule were found
    
   .. exn:: maxed nested rewriting
    
        There were too many nested rewriting. This is to avoid infinite rewriting loops.

      
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
    
    Assert that exec@_ implies exec@_ for all previous
    timestamps. 

    Given as input a timestamp :g:`ts`, this tactic produces two new
    sub-goal, requiring to prove that :g:`happens(ts)` holds and that
    :g:`exec@ts` also holds. The fact that :g:`(forall (t:timestamp),
    t <= ts => exec@t)` is added to the current goal.


.. tact:: project
    
    Turn a local goal on a :term:`multi system` into one goal for each
    single system comprising of the multi-system.

.. tact:: rewrite equiv
    
    Use an equivalence to rewrite a reachability goal.

    .. todo::
       TODO


.. tact:: slowsmt
    
    Version of the :tacn:`smt` tactic with higher time limit. 
      
.. tact:: smt
   :name: smt    
    
    Tries to discharge the current goal using an SMT solver. 
      

.. tact:: subst @term, @term

    Replaces all occurences of a variable by a value it must be equal
    to.  Call as :g:`subst x, t`, if :g:`x = t` where :g:`x` is a
    variable, substitute all occurences of :g:`x` by :g:`t` and remove
    :g:`x` from the :term:`logical variables <logical_var>`.
    
    
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
     :g:`equiv(if phi then t1 else t2, if phi then u1 else u2)`
     invoking :g:`cs phi` results in two sub-goals:
     :g:`equiv(phi, t1, u1)` and :g:`equiv(phi, t2, u2)`.

   .. exn:: Argument of cs should match a boolean.
      :undocumented:

   .. exn:: Did not find any conditional to analyze.
      :undocumented:

.. tace:: deduce
    
    `deduce i` removes the ith element from the biframe when it can be
    computed from the rest of the biframe.
    `deduce` try to deduce the biframe with the first equivalence in the
    hypotheses it finds. 

    .. todo:: 
       TODO

.. tace:: diffeq
    
    Closes a reflexive goal up to equality 
      
    .. todo::
       Charlie: Here, still waiting to have clean multisystem
       support in reachabiliy goal to clarify this..
      

.. _section-crypto-tactics:

Cryptographic tactics
---------------------

Common tactics
~~~~~~~~~~~~~~


.. tacn:: fresh @position
   :name: fresh

   .. todo::    
      TODO

   
Local tactics
~~~~~~~~~~~~~


.. tact:: cdh
   
    Usage: cdh H, g.
    Applies the CDH assumption (including squareCDH) on H using generator
    g. 

   .. todo::    
      TODO
       

.. tact:: collision
    
    Collects all equalities between hashes occurring at toplevel in message
    hypotheses, and adds the equalities between messages that have the same
    hash with the same valid key. 
      
    Usage: collision [H]

    .. todo::    
       TODO


.. tact:: euf
    
    Apply the euf axiom to the given hypothesis name. 

.. todo::    
       TODO      
       

.. tact:: gdh
    
    Usage: gdh H, g.
    Applies the GDH assumption (including squareGDH) on H with generator
    g. 
      
    .. todo::    
       TODO       

.. tact:: intctxt
    
    Apply the INTCTXT axiom to the given hypothesis name. 
      
    .. todo::    
       TODO       


Global tactics
~~~~~~~~~~~~~~


.. tace:: cca1
    
    Apply the cca1 axiom on all instances of a ciphertext. 
      
    .. todo::    
       TODO
    
.. tace:: ddh
    
    Closes the current system, if it is an instance of a context of
    ddh. 
      
    Usage: ddh H1, H2, H3, H4

    .. todo::    
       TODO    

.. tace:: enckp
    
    Keyprivacy changes the key in some encryption
    subterm. 
      
    Usage: enckp i, [m1], [m2]

    .. todo::    
       TODO    


.. tacn:: prf @position
   :name: prf

    .. todo::        
       TODO why optional message in Squirrel tactic; also fix help in tool    
       

.. tace:: xor
    
    Removes biterm (n(i0,...,ik) XOR t) if n(i0,...,ik) is
    fresh. 
      
    Usage: xor i, [m1], [m2]
    
    .. todo::    
       TODO    

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
      
.. tacn:: show todo
    
    Print the messages given as argument. Can be used to print the values
    matching a pattern. 
      
