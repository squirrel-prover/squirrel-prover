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

Judgements
==========

A proof state is described within a judgment. A judgment is made of a set of goals that need to be proved. Each goal is linked to some systems, the set of :term:`logical variables <logical_var>`, the current set of hypothesis, and the conclusion to reach. 

The display of each current goal whitin the judgment depends on its type.

Logical variables
-----------------

:gdef:`Logical variable <logical_var>` are free variables in a current goal. Such variables are implicitly quantified based on their type and tag.

Hypotheses
----------

.. prodn:: hypothesis_id ::= identifier

.. todo::
   Adrien: todo
   
Local goal
----------

The general layout for a local goal is as follows:

.. squirreldoc::
   
      [goal> Focused goal (x/N):
      System: currentSystem
      Variables: vars
      H_1: formula_1
      ...
      H_k: formula_k
      —————————————-
      conc


Here, we are proving the goal number :g:`x` out of :g:`N` goals. The system of the current goal is :g:`currentSystem`, a prettified :n:`@system_expr`, :g:`vars` is a set of fullet specified variables with names, types and tags. Each hypothesis is identified by its name :g:`H_i` and each :g:`formula_i` as well as :g:`conc` is a :term:`local formula`.
     

Global Goal
-----------

The general layout for a global goal is similar to the local one except that now:

 * :g:`currentSystem` can also be a prettified :n:`@global_decl` of
   the systems used for interpreting the local formulas and the equiv
   predicates.
 * each hypothesis and the conclusion can be a :term:`global formula`.


When the conclusion is a single :n:`equiv(@term,...,@term)` predicate,
all the bi-terms that need to be proved equivalent are displayed as a
numbered list.

.. example:: Initial judgment for observational equivalence
   
	     Consider a goal for observational equivalence, where the
	     frame is enriched with some public key, as follows:
	     :g:`global goal [myProtocol] obs_equiv (t:timestamp) :
	     [happens(t)] -> equiv(frame@t, pk(sk)).`. When starting
	     its proof, after doing :g:`intro H`, the goal is
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

In the context of a (sub)goal, an :gdef:`assumption` refers to
an hypothesis in the current goal, or
an axiom or previously proven goal.
Assumptions are referred to by their identifier when used in
tactics.

.. prodn::
  assumption ::= @hypothesis_id | @statement_id

Tactics that apply to equivalence goals may take a natural number
as argument to identify one item in the equivalence. This is represented
using the :token:`position` token.

.. prodn::
  position ::= @natural


When a tactic expect a term (which can then be a local formula), it is allowed to underspecify the term by using holes of the form :g:`_`.

Such term patterns are produced by appending to the production of :n:`term` the hole construct:

.. prodn:: term_pattern ::= ...
	   | _

Arguments that are :n:`@term_pattern` will first by patterned match against the conclusion of the goal, the match being the actual term passed to the tactics.

Intro patterns
~~~~~~~~~~~~~~
  
The way new hypothesis are introduced by tactics can be defined with so-called intro patterns. We inherit the definition of intro patterns from the corresponding `coq documentation <https://coq.inria.fr/refman/proof-engine/tactics.html#intro-patterns>`_, restricted to the notation :g:`[ ]` for And/Or introductions.

.. prodn::
   intropattern ::= @assumption
                | @variable
		| *
		| _
		| {+ @intropattern }
		| [ {+ @intropattern } ]
		| [ {+/ @intropattern } ]

This behaves as follows:

* :n:`@assumption` and :n:`@variable` are used to specify the names of the introduced hypothesis and variables. :n:`*` is used to select automatically a name, and :n:`_` to not give any.
* a sequence of patterns is applied sequentially.
* :n:`[ @assumption ... @assumption]` is used to split a conjunction and name all the introduced sub hypothesis.
* :n:`[ @assumption / ... / @assumption]` is used to split a disjunction, thus creating subgoals.
  
We also have :gdef:`extended intro patterns <ext intro pat>`, that apply some additional transformations to the obtained hypothesis.

.. prodn::
   ext_intropattern ::=  {+ @intropattern | @ext_intropattern }
                | ->
		| <-
		| //
		| /=
		| //=
		| @/@macro

The extended features are:

* :g:`->` and :g:`<-` will try to use the introduced hypothesis to rewrite the goal in the directio given by the arrow.
* :g:`//` applies :g:`try auto` in all subgoals, leaving the one not closed without any simplification.
* :g:`/=` applies :tacn:`simpl` to all subgoals.
* :g:`//=` combines both previous operators.
* :g:`@/@macro` expands the given macro in the hypothesis.  
  

  


Proof terms
-----------

Proof terms are used by several tactics as a convenient way to combine
and (partially) apply :term:`assumptions <assumption>` in order to
derive new facts.

.. prodn::
   proof_term ::= @assumption {* @pt_arg}

.. prodn::
   pt_arg ::= @assumption | @sterm | (% @proof_term)

Note that the grammar for proof term arguments :token:`pt_arg` is
ambiguous (because of the :token:`assumption` and :token:`sterm`
productions). When this happens, Squirrel tries to desambiguate using
the context.

.. note::
   The :n:`(% @proof_term)` syntax is experimental, and is subject to
   change in the future.

   
.. todo::
   Charlie: not trying to do that^^

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

The :g:`constr` transformation replaces trace (sub)formulas that
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

     Attempt to automatically prove a subgoal.

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
    goal into several subgoals, automatically closing only the trivial
    goals closed by :tacn:`true` and :tacn:`assump`.

    When the conclusion of the goal is a global formula which only contains
    a local formula, the goal is then turned into a local formula. Otherwise
    this does nothing.
    
    Additionaly If the :term:`option` :g:`autoIntro` is set to true, introductions
    are also made automically.



.. tacn:: simpl {? @simpl_flags}

     Simplify a subgoal, working on both hypotheses and conclusion.
     This tactic always succeeds, replacing the initial subgoal with
     a unique simplified subgoal.

     The tactic uses the :ref:`reduction engine <reduction>`
     with the provided flags.

     When the conclusion of the goal is a conjunction, the tactic
     will attempt to automatically prove some conjuncts (using :tacn:`auto`)
     and will then return a simplified subgoal without these conjuncts.
     In the degenerate case where no conjunct remains, the conclusion
     of the subgoal will be :g:`true`.

     When the conclusion of the goal is an equivalence, the tactic
     will automatically perform :tacn:`fa` when at most one of the remaining
     subterms is non-deducible. It may thus remove a deducible item
     from the equivalence, or replace an item :g:`<u,v>` by :g:`u`
     if it determines that :g:`v` is deducible.

         

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
   | @tactical => @ext_intropattern


   
The semi-column :g:`;` is used for sequential composition. The second tactical is then applied to all subgoals created by the first one, unless number of subgoals are specified. The :g:`+` performs a or-else when the first tactical fails.

The reminder behaves as follows:

.. tacn:: by @tactical
	  
   Fails unless the tactical closes the goal.

.. tacn:: nosimpl @tactical

  Call tactic without the subsequent implicit use of simplications.
  This can be useful to understand what's going on step by step.
  This is also necessary in rare occasions where simplifications are
  actually undesirable to complete the proof.

.. tacn:: try @tactical

  Try to apply the given tactic. If it fails, succeed with the
  subgoal left unchanged.

.. tacn:: repeat @tactical

  Apply the given tactic, and recursively apply it again on the
  generated subgoals, until it fails.

Finally, :g:`tactical => ext_intropattern` is syntactic sugar for :g:`tactical; intros ext_intropattern`
  
Common errors
-------------

.. exn:: Out of range position.v

     Argument does not correspond to a valid equivalence item.


Tactics
=======

Tactics are organized in three categories:

 - logical, that rely on general logical properties;
 - structural, that rely on properties of protocols and equality;
 - cryptographic, that rely on some cryptographic assumption that must be
   explicitly stated.

In addition, they are also split between tactics applicable to :term:`local goals <local goal>` only, :term:`global goals <global goal>` only, or tactics common to both types of goals. Remark that the type of the current goal may evolve overtime when using tactic.

Additionaly, we also have a few utility tactics listed at the end.


Logical tactics
---------------

Common tactics
~~~~~~~~~~~~~~

.. tacn:: admit {? @position}
   :name: admit     

    Admit the current goal, or admit an element from a 
    biframe by refering to its position. 


.. tacn:: assumption {? @assumption}
   :name: assump
      
    Concludes if the goal or false appears in the
    hypotheses. The corresponding hypothesis may be directly given as argument.


.. tacn:: case {| @assumption | @term_pattern}
	  
    Perform a case analysis over the given arugment, which can either be:
    
     - an assumption which is a disjunction, split into several cases;
     - a term of type timestamp, in which case the cases are over the fact that this timestamp must be equal to one of the actions of the system instantiated with some newly existantial indices.
      
      
     
.. tacn:: dependent induction {? @variable}
	  
    Apply the induction scheme to the conclusion. If no argument is specified, the conclusion must be a universal quantification over a well-founded type. Alternatively, a variable of the goal can be given as argument, in which case the goal is first generalized as the universal quantification over the given variable before proceeding with the induction.

   .. todo::

      Charlie: Discussions needed, check out discord + cleanup_induction branch    
    

.. tacn:: destruct @assumption {? as @ext_intropattern}
	  
    Destruct an hypothesis based on its topmost destructable operator (existantial quantification, disjunction or conjunction). An optional :term:`extended introduction pattern <ext intro pat>`  can be given.
    
    .. example:: Destruct 
       
       If there exists an hypthesis :g:`H: A \/ (B /\ C)`, the command
       :g:`destruct H as [H1 | [H2 H3]]` will remove the H hypothesis
       and introduce instead:
	  
       .. squirreldoc::
	  
	  H1: A
	  H2: B
	  H3: C
      
       

.. tacn:: exists {* @variable}
	  
    Introduce the existentially quantified variables in the conclusion of the
    judgment, using the arguments as names for the existential witnesses.          
       

.. tacn:: generalize {+ @variable} {? as {+ @variable}}
	  
    Generalize the goal on some variables, that is, make the goal universally quantified over the given variables. New names for the now universally quantified variables can be specfied.

.. tacn:: generalize dependent  {+ @variable} {? as {+ @variable}}
	  
    Generalize the goal and hypotheses on some terms. Hypothesis that depend on the specified variable are first pushed back inside the goal, before the goal is generalized.              

.. tacn:: have {|@term_pattern|@term_pattern as @ext_intropattern|@ext_intropattern : {|@term_pattern|@global_formula}| @intropattern := @proof_term}

    This is used to introduce a new hypothesis that will have to be proved in a new goal. The multiple usages behave as follow:

     - :g:`have t` add as a new hypothesis a :token:`term` :g:`t` of type :g:`bool`, and the corresponding goal is created;
     - :g:`have t as intro_pat` behaves similarly but also apply the given :token:`ext_intropattern` to the newly introduced hypothesis;
     - :g:`have intro_pat : formula_or_global_f` also works for both local and global formulas;
     - :g:`have intro_pat := proof_term` first computes the given :token:`proof_term` before proceeding.
                    
.. tacn:: id

   The identity tactic, which does nothing.
   
   .. todo::

      Charlie: Maybe add justification of why we have this tactic, but I don't know it.

.. tacn:: induction {? @variable} todo
	  
  
   .. todo::

      Charlie: Discussions needed, check out discord + cleanup_induction branch


.. tacn:: intro {+ @ext_intropattern}
	  
    Introduce topmost connectives of conclusion formula by following the sequence of :token:`ext_intropattern`, when it can be done
    in an invertible, nonbranching fashion.

.. tacn:: left
	  
    Reduce a goal with a disjunction conclusion into the goal where the
    conclusion has been replaced with the first disjunct. 


.. tacn:: reduce {? @simpl_flags}

     Reduce all terms in a subgoal, working on both hypotheses and conclusion.
     
     This tactic always succeeds, replacing the initial subgoal with a
     unique subgoal (which may be identical to the initial one).

     The tactic uses the :ref:`reduction engine <reduction>`
     with the provided flags.
     
.. tacn:: remember @term_pattern
	  
    Substitute the given term by a fresh variable and adds as hypothesis the equality between the term and the new variable.
      
       
.. tacn:: revert @assumption
	  
    Take an hypothesis H, and turns the conclusion C into the implication H
    => C. 
             
.. tacn:: right
	  
    Reduce a goal with a disjunction conclusion into the goal where the
    conclusion has been replaced with the second disjunct. 

.. tacn:: split
	  
    Split a conjunction conclusion, creating one subgoal per
    conjunct. 

       
.. tacn:: use @assumption {? with {+ variables}} {? as @ext_intropattern}
   :name: use	   
	  
    Instantiate a lemma or hypothesis based on the given. The optionnaly given variables are used to instantiate the universally quantified variables of the lemma.
    An intropattern can also be specified.
          

      
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
    and must return a boolean.  This tactic creates two subgoals
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
       and creats two subgoal, asking to prove the two following formulas:

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


.. tacn:: localize @assumption as @ext_intropattern
	  
    Change a global hypothesis containing a reachability formula to a
    local hypothesis, and applies the given :term:`extended
    introduction pattern <ext intro pat>` to the new hypothesis.
      


.. tace:: memseq
	  
    Prove that a biframe element appears in a sequence of the biframe. 

    .. todo::
       Charlie: hum. There are no examples nor test for this function.
       It should be tested before being documented (don't know who did it)
       

.. tace:: refl
	  
    Closes a reflexive goal, where all items must be reflexive. As an
    overapproximation, it only works if the goal does not contain
    variable or macros, as those may break reflexivity.


.. tace:: splitseq @position: (fun @binders => @term)
	  
   Splits a sequence according to some boolean test, replacing the
   sequence by two subsequence.

   The function passed as argument must be a function taking as
   argument a variable of the same type as the sequence and must
   return a boolean.

   .. example:: Splitting a sequence
      
      Called over a conclusion of the form :g:`0: seq(x:message =>
      value)`, the tactic :g:`splitseq 0: (fun y:message => some_test)` replaces the conclusion by:

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

    .. todo::
       Charlie:: this is not used either. It is deprecated I think.

Structural tactics
------------------


Common tactics
~~~~~~~~~~~~~~

      
.. tacn:: apply
   :name: apply	  
	  
    Matches the goal with the conclusion of the formula F provided (F can be
    an hypothesis, a lemma, an axiom, or a proof term), trying to instantiate
    F variables by matching. Creates one subgoal for each premises of
    F.

   .. todo::
      TODO
     

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

.. tacn:: expand {+ @macro | @macro@@term }
	  
    Expand all occurences of the given macros, either fully specified with an action or simply a type of macro, inside the goal.
    
.. tacn:: expandall
	  
    Expand all possible macros in the sequent. 
             

.. tacn:: fa {|@position | @term_pattern}
   :name: fa

   .. todo::
      TODO

.. tacn:: namelength @term, @term
	  
    Adds the fact that two names have the same
    length. The two arguments must the indeed be a :term:`name`.
      
    Usage: namelength m1, m2  


.. tacn:: rewrite
	  
    .. todo::
       Big todo with many options, see tutorial advanced for some starting point.
      
       

      
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
    subgoal, requiring to prove that :g:`happens(ts)` holds and that
    :g:`exec@ts` also holds. The fact that :g:`(forall (t:timestamp),
    t <= ts => exec@t)` is added to the current goal.


.. tact:: project
	  
    Turn a goal on a :term:`bi-system` into one goal for each
    projection of the bi-system.
      


.. tact:: rewrite equiv
	  
    Use an equivalence to rewrite a reachability goal.

    .. todo::
       TODO


.. tact:: slowsmt
	  
    Version of the :tacn:`smt` tactic with higher time limit. 
      
    Usage: slowsmt   

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
     invoking :g:`cs phi` results in two subgoals:
     :g:`equiv(phi, t1, u1)` and :g:`equiv(phi, t2, u2)`.

   .. exn:: Argument of cs should match a boolean.
      :undocumented:

   .. exn:: Did not find any conditional to analyze.

        some doc

	


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

	
Utility tactics
---------------

.. tacn:: clear @assumption
	  
    Drop the specified hypothesis. 


.. tacn:: help {? {|@tacn|concise}}
	  
    When used without argument, display all available commands. It can also display the details for the given tactic name, or display or more concise list. It is a tactic and not a command, it can only be used inside proofs.

.. tacn:: lemmas
	  
    Print all proved lemmas. This is usefull to know which lemmas can be used through the :tacn:`use` or :tacn:`apply` tactics.



.. tacn:: print {? identifier}

    By default, shows the current system. Otherwise, gives the definition of the given symbol (that may be a macro or a system).

.. tacn:: prof
	  
    Print profiling information. 


.. tacn:: search  todo
	  
    Search lemmas containing a given pattern. 
      
    Usage: search   

    
.. tacn:: show  todo
	  
    Print the messages given as argument. Can be used to print the values
    matching a pattern. 
      
    Usage: show m  
    
