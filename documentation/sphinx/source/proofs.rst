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
             

.. tacn:: fa {|@position | @term_pat | {+ , @fa_arg}}
   :name: fa

   This tactic is a function application, it simplifies a goal by
   removing the head function symbol as follows:
   
   * in a local goal with conclusion :g:`f(u)=f(v)`, the conclusion is
     replaced with :g:`u=v`. This produces as many subgoals as argument
     of the head function symbol. For a local goal, the tactic takes no
     arguments.
   * in a global goal containing :g:`f(u1,...,un)`, one can prove it by
     proving that the goal containing the sequence :g:`u1,...,un` is
     diff-equivalent.

     
   In the global goal setting, the target hypothesis can be selected
   with its :n:`@position`. Otherwise, by giving a :n:`@term_pat`, the
   function application will target the first hypothesis matching the
   pattern. At least one such hypothesis must exist.

   The function application can be made more complex with:
	  
   .. prodn::
      fa_arg ::= {| ! | ?} @term_pat

   The different options behaves as follows:
   
   * calling :g:`fa !t` repeats the function application as much as
     possible over all possible hypothesis.
   * :g:`fa ?t` tries to apply function application one
     matching the pattern, but does not fail if no match is
     found.
   * :g:`fa t1, t2, ...` is syntactic sugar for
     :g:`fa t1; fa t2; ...`.
	 
    

.. tacn:: namelength @term, @term
    
    Adds the fact that two names have the same
    length. The two arguments must the indeed be a :decl:`name`.

    .. todo:: Charlie: Don't we want to deprecate this one?  Some
       tests just need to be fixed, but otherwise no more example use
       this.  

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

.. tace:: deduce {? @position}
    
    :g:`deduce i` removes the ith element from the biframe when it can
    be computed from the rest of the biframe. Without any argument, it
    will remove the first equivalence that can be dropped, if it
    exists.

    Here, the fact that the biframe element :g:`u` can be computed
    from the other biframe elements :g:`x,y,...` means that there
    exists a context :g:`C` made of function applications such that
    :g:`u` is equal to :g:`C[x,y,..]`.

    This rely on some automated reasoning that may not be complete,
    notably w.r.t. equational theories. Regarding macros, some partial
    support is enabled, typically that for any timestamp :g:`t`,
    :g:`frame@pred(t)` allows to deduce :g:`input@t`, all :g:`frame@t'`
    for :g:`t' < pred(t)`, as well as the :g:`output@t'` for whenever
    :g:`exec@t'` is true.

    

    .. todo::
       Charlie: do we want an exhaustive description of the deduce algo?
   

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
probabilistic properties of random samplings and primitves. For each one, if pertinent, we refer to the corresponding classical computational assumption, as well as

Occurence formula
~~~~~~~~~~~~~~~~~

Several reasonings imply to be able to track how a given name is
used. For instance, if the name :g:`n` does not ocurr at all in term
:g:`t`, then :g:`n=t` is false with overwelming probability. To apply
a cryptographic assumption that needs a secret key, one need to check
that all occurences of the secret key are valid ones, e.g. only used
in key position of the corresponding primitive.

Over macro-free terms, collecting occurences is simply equivalent to
looking at the subterms. However, if some macros occur in :g:`t`,
typically :g:`input@ts` or :g:`output@ts`, we need to look through all
the actions that may have happened before :g:`ts` and may depend on
:g:`n`.

We define here how to build an :gdef:`occurence formula` that will be
reused in several tactics description. For any name :g:`n`, any term
:g:`t` and a set of allowed patterns :g:`pats` (patterns built over
the name :g:`n` and function applications), we define the formula
:g:`occurs(n,t,pats)` as the conjunction of conditions under which it
is possible that :g:`n` occurs in :g:`t` without following one of the
allowed pattern of `pats`:

* whenever :g:`t` contains as a subterm an occurence :g:`n` that does not follow any of the allowed patterns :g:`pats`, the formula is :g:`true`.
* whenever :g:`t` contains a :ref:`system-defined macro<section-system-macros>`, :g:`macro@ts`, if `ts` is a concrete action, we simply unfold the definition of the macro, and whenever is it not concrete, we collect all actions of the form :g:`A1` such that :g:`n` occurs in the definition of the action not as an allowed pattern, and the formula :g:`A1<=ts` is added to the conjunction of :g:`occurs(n,t,pats)`.

Occurs is of course generally defined for indiced names that may
occured in index actions.

.. example:: Basic name occurence
	     
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

      
   To reason about the encrypted message, the key :g:`k` needs to be secret, and thus the dynamic corruption should not have happened. This intuition is captured by the formula :g:`occurs(k,input@B,enc(_,r,k))`, which is equal to :g:`Corr < B`.  

   
This formula may be imprecise, for example due to states.

.. example:: Imprecise state occurence

   .. squirreldoc:: 
      name n : message

      mutable s = n.
      
      channel c

      system (A: out(c,s) | B :in(c,x);out(c,x))  .      
      
   Here, :g:`n` occurs only inside the :g:`init` action, where the
   mutable state is initialized with value :g:`n`. The formula
   :g:`occurs(n,input@B,none)` is then equal to :g:`init < B`.
   However, the occurence can happen only if :g:`A` did occur between
   :g:`init` and :g:`B` to reveal the value of the state.


We define a precise variant :g:`precise_occurs(n,t,pats)`, that tracks
more precisly the usages of the states, and also adds the condition
that the correct value of the state is revealed if a state can contain
an occurence of :g:`n`.

We also generalize occur to allow for collecting multiple name
occurences at once, useful when we want to allow patterns depending on
two names at once (see e.g. :tacn:`gdh` or :tacn:`ddh`).
   
Common tactics
~~~~~~~~~~~~~~


.. tacn:: fresh {? ~precise_ts} {| @position | @hypothesis_id }
   :name: fresh

   Fresh is an unconditionaly sound tactic relying on the fact that
   two fresh names, that is, two names never seen by the attacker
   before, are indistinguishable. This can be exploited in multiple
   ways, for instance to remove a fresh name from an equivalence, or
   to state that a term can never be equal to a fresh name.
   
   In a local goal, called over an hypothesis of the form :g:`t=n` for
   some name :g:`n` over a current goal formula :g:`phi`, turns the
   goal into a formula :g:`occur(n,t,none) => phi` (see the
   definition of the :term:`occurence formula`)

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
      
   In an equivalence goal, the tactic must be applied to a biframe
   element :g:`i` of the form :g:`diff(nL,nR)`.  If we denote by
   :g:`bf` the biframe, the biframe element is then replaced by

   .. squirreldoc::
      if not(diff(occur(nL,bf,none),occur(n,bf,none))) then
        zero
      else
        diff(nL,nR)

   In all cases, the :g:`precise_ts` makes the tactic use
   `precise_occur` instead of `occur`.

   Latest formal Squirrel description: :cite:`bkl23hal` (Appendix F).

Local tactics
~~~~~~~~~~~~~


.. tact:: cdh @hypothesis_id, @term
   :name: cdh

   This tactic applies the Computational Diffie-Helman assumption (see
   e.g. :cite:`okamoto2001gap`), stating that given two groups elents
   :g:`g^a` and :g:`g^b` it is difficult to compute :g:`g^(ab)`.

   A cdh, ddh or gdh :term:`group declaration <group declaration>` must have been
   specified. For a group with generator :g:`g` and exponentiation
   :g:`^`, calling :g:`cdh M, g` over a message equality :g:`M` of the
   form `t=g^{a b}` will replace the current goal :g:`phi` by
   :g:`occur(a,t,g^a) || occur(b,t,g^b) => phi` (see the
   definition of the :term:`occurence formula`). If :g:`a`
   and :g:`b` only occur as :g:`g^a` and :g:`g^b`, the goal is then
   closed automatically.
    
   .. warning::
      This is a work in progress, a formal description of the rule is pending.
             
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
   message equality :g:`M` of the form :g:`t = h(m,k)` or :g:`h(m,k)=t`.  The
   tactic then create a first new subgoal asking to prove that the key
   is only used in correct position, that is a goal with conclusion
   :g:`not(occur(k,goal,h(_,k))`.  The tactics then collects all
   possible occurence of honest hash :g:`h(u,k)` inside :g:`t`, and
   for each of them, creates a subgoal with a new hypothesis stating
   that :g:`m=u`. If such an occurence happens under a macro, the goal
   will state that the computation must have happened before.

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
   (see the definition of the :term:`occurence formula`).

    .. warning::
       This is a work in progress, a formal description of the rule is pending.       

.. tact:: intctxt @hypothesis_id
   :name: intctxt
	  
    This tactics applies the INTCTXT assumption (see
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
    created (when it is not trivially true).

    In additition, a goal asking to prove that all randomness used for
    encryption are disjoint and fresh (when it is not trivially true).

    Latest formal Squirrel description: :cite:`bdjkm21sp`.      


Global tactics
~~~~~~~~~~~~~~


.. tace:: cca1
   :name: cca1
	  
    Apply the cca1 axiom on all instances of a ciphertext.
      
    .. todo::    
       TODO

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
   to false (see the definition of the :term:`occurence formula`).

   Latest formal Squirrel description: :cite:`bdjkm21sp`.
       
.. tace:: enckp @position {? @term_pat } {? @term }
   :name: enckp

   ENC-KP assumes that a symmetric or an asymmetric encryption scheme
   does not leak any information about the public (or secret) key
   used to encrypt the plaintext. It is based on the IK-CPA notion of
   :cite:`bellare2001key`.

   The tactic can be called over a biframe element containing a term of
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
	 
      On a biframe element of the form
      
      .. squirreldoc::
	 i : enc(n,r,diff(pk(k1),pk(k2)))
	 
      calling the tactic :g:`enckp i` will simplify the biframe
      element by only keeping the key on the left, yielding
      
      .. squirreldoc::
         i: enc(n,r,pk(k1))

   The tactic expects as argument:
   
   • the number identifying the biframe element;
   • optional: the encryption term over which to apply the tactic;
   • optional: the new key by which to replace the key.


   .. example:: Switching key with ENC-KP
		
      On a biframe element of the form
      
      .. squirreldoc::	 
	 i: enc(n,r,m)

      the tactic :g:`enckp i, k` will simplify the biframe element by using the specified
      key, yielding
      
      .. squirreldoc::
	 i: enc(n,r,pk(k))


   .. example:: Targeted ENC-KP application
		   
      On a biframe element of the form
      
      .. squirreldoc::
	 i: ⟨ enc(n,r,m),m'⟩

      the tactic :g:`enckp i,enc(n,r,m), k` will simplify the biframe
      element by using the specified key, yielding
      
      .. squirreldoc::
	 i: ⟨ enc(n,r,pk(k)),m '⟩


   To apply the enckp tactic, the key :g:`k` must be such that :g:`occur(k,biframe,(enc(_,_,k), dec(_,k))` is trivially false. (or :g:`occur(k,biframe,(pk(k), dec(_,k))`) for the asymmetric case).

   When it is not trivially true, a subgoal is created to prove the
   freshness of the random used in the encryption, with the conclusion
   :g:`occur(r,biframe,enc(n,r,m))`.

   In the symmetric case, an additional check is performed ensuring
   that all encryptions are made with distinct fresh randoms (and not
   that just the encryption we are looking at is fresh).
   
   Latest formal Squirrel description::cite:`bdjkm21sp`.
      
.. tacn:: prf @position
   :name: prf

   .. todo::        
      TODO why optional message in Squirrel tactic; also fix help in tool    
       

   Latest formal Squirrel description: :cite:`bkl23hal`.
       
.. tace:: xor
    
   Removes biterm (n(i0,...,ik) XOR t) if n(i0,...,ik) is
   fresh.

   Usage: xor i, [m1], [m2]
    
   .. todo::    
      TODO

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
      
.. tacn:: show todo
    
    Print the messages given as argument. Can be used to print the values
    matching a pattern. 
      
