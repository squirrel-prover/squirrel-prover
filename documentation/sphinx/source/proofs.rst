.. _section-proofs:

.. How to write proofs in Squirrel

------
Proofs
------

.. todo::
   Charlie: for each tactic, the name contains todo if it was never touched, and the description is just imported from help.

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

TODO

Logical variables
-----------------

:gdef:`Logical variable <logical_var>` TODO

   
Generalities
============

Tactic arguments
----------------

In the context of a (sub)goal, an :gdef:`assumption` refers to
an hypothesis in the current goal,
a previously proved goal, or
a previously declared axiom.
Assumptions are referred to by their identifier when used in
tactics.

.. prodn::
  assumption ::= @identifier

Tactics that apply to equivalence goals may take a natural number
as argument to identify one item in the equivalence. This is represented
using the :token:`position` token.

.. prodn::
  position ::= @natural

The way new hypothesis are introduced by tactics can be defined with so-called intro patterns. We inherit the definition of intro patterns :token:`intropattern` from the corresponding `coq documentation <https://coq.inria.fr/refman/proof-engine/tactics.html#intro-patterns>`_, restricted to the notation :g:`[ ]` for And/Or introductions.

.. todo:: Charlie: the previous intropattern token definition does not perfectly work, as future cross-references :token:`intropattern` are not clickable links, see e.g. the :tacn:`destruct` tactic where the link is not clickable.
  
.. todo:: most (all?) tactics take terms and formulas as patterns,
	  with an implicit filling of the holes by matching against the subgoal's
	  conclusion; document this, and also decide whether arguments are shown
	  as :token:`term`, :token:`formula`, :token:`pattern`,
	  :token:`formula_pattern`, etc.

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
   Todo

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
	  
    Simplify a goal, without closing it or any of the created subgoals.
    This is automatically called after each tactic.

    The tactic uses the :ref:`reduction engine <reduction>`
    with the flags :g:`rw,beta,proj`.

    When the conclusion of the goal is a conjuction,

    When the conclusion of the goal is an equivalence,    

    .. todo::
       Charlie: does anybody knows exactly what happens wihtout
       reverse engineering the code?
    
    Addiotionaly If the :term:`option` :g:`autoIntro` is set to true, introductions
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

.. todo:: David: I'm not sure we want to document tacticals using the same
	  role as elementary tactics, I did it like this for now just so the
	  references to try and repeat in the appendix work.

.. tacn:: nosimpl @tactic

  Call tactic without the subsequent implicit use of simplications.
  This can be useful to understand what's going on step by step.
  This is also necessary in rare occasions where simplifications are
  actually undesirable to complete the proof.

.. tacn:: try @tactic

  Try to apply the given tactic. If it fails, succeed with the
  subgoal left unchanged.

.. tacn:: repeat @tactic

  Apply the given tactic, and recursively apply it again on the
  generated subgoals, until it fails.


Common errors
-------------

.. exn:: Out of range position.

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


.. tacn:: case {| @assumption | @term}
	  
    Perform a case analysis over the given arugment, which can either be:
    
     - an assumption which is a disjunction, split into several cases;
     - a term of type timestamp, in which case the cases are over the fact that this timestamp must be equal to one of the actions of the system instantiated with some newly existantial indices.
      
      
     
.. tacn:: dependent induction {? @variable} todo
	  
    Apply the induction scheme to the conclusion. If no argument is specified, the conclusion must be a universal quantification over a well-founded type. Alternatively, a variable of the goal can be given as argument, in which case the goal is first generalized as the universal quantification over the given variable before proceeding with the induction.

   .. todo::

      Charlie: Discussions needed, check out discord + cleanup_induction branch    
    

.. tacn:: destruct @assumption {? as @intropattern}
	  
    Destruct an hypothesis based on its topmost destructable operator (existantial quantification, disjunction or conjunction). An optional And/Or introduction pattern can be given.
    
    .. example::
       
       If there exists an hypthesis :g:`H: A \/ (B /\ C)`, the command
       :g:`destruct H as [H1 | [H2 H3]]` will remove the H hypothesis and introduce instead:
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

.. tacn:: have {|@term|@term as @intropattern|@intropattern : {|@term|@global_formula}| @intropattern := @proof_term}

    This is used to introduce a new hypothesis that will have to be proved in a new goal. The multiple usages behave as follow:

     - :g:`have t` add as a new hypothesis a :token:`term` :g:`t` of type :g:`bool`, and the corresponding goal is created;
     - :g:`have t as intro_pat` behaves similarly but also apply the given :token:`intropattern` to the newly introduced hypothesis;
     - :g:`have intro_pat : formula_or_global_f` also works for both local and global formulas;
     - :g:`have intro_pat := proof_term` first computes the given :token:`proof_term` before proceeding.
                    
.. tacn:: id

   The identity tactic, which does nothing.
   
   .. todo::

      Charlie: Maybe add justification of why we have this tactic, but I don't know it.

.. tacn:: induction {? @variable} todo
	  
  
   .. todo::

      Charlie: Discussions needed, check out discord + cleanup_induction branch


.. tacn:: intro {+ @intropattern}
	  
    Introduce topmost connectives of conclusion formula by following the sequence of :token:`intropattern`, when it can be done
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
     
.. tacn:: remember @term
	  
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

       
.. tacn:: use @assumption {? with {+ variables}} {? as @intropattern}
   :name: use	   
	  
    Instantiate a lemma or hypothesis based on the given. The optionnaly given variables are used to instantiate the universally quantified variables of the lemma.
    An intropattern can also be specified.
          

      
Local tactics
~~~~~~~~~~~~~

.. tact:: true
	  
    Closes a goal when the conclusion is true. 

      
Global tactics
~~~~~~~~~~~~~~

.. tace:: byequiv todo
	  
    transform an equivalence goal into a reachability
    goal. 
      
    Usage: byequiv   
  

.. tace:: constseq todo
	  
    simplifies a constant sequence 
             
.. tace:: enrich @term
	  
    Enrich the equivalence goal with the given term, that can either be of type :g:`message` or :g:`bool`. Note that this changes the number of items in the equivalence, and if added before other tactics may break later references.


.. tacn:: localize  todo
	  
    Change a global hypothesis containing a reachability formula to a local
    hypothesis. 
      
    Usage: localize H1, H2  


.. tace:: memseq todo
	  
    prove that an biframe element appears in a sequence of the biframe. 
      
       

.. tace:: refl
	  
    Closes a reflexive goal, where all items must be reflexive. As an overapproximation, it only works if the goal does not contain variable or macros, as those may break reflexivity.


.. tace:: splitseq todo
	  
    splits a sequence according to some boolean 
      
       

.. tace:: sym
	  
    Swap the left and right system of the equivalence goal.

.. tace:: trans todo
	  
    Prove an equivalence by transitivity. 
      

Structural tactics
------------------


Common tactics
~~~~~~~~~~~~~~

      
.. tacn:: apply  todo
   :name: apply	  
	  
    Matches the goal with the conclusion of the formula F provided (F can be
    an hypothesis, a lemma, an axiom, or a proof term), trying to instantiate
    F variables by matching. Creates one subgoal for each premises of
    F.
    Usage
    apply H.
    apply lemma.
    apply axiom. 
      

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
      
    Usage: depends ts1, ts2  


.. tacn:: expand  todo
	  
    Expand all occurences of the given macro inside the
    goal. 
      
    Usages: expand H
            expand m
            expand f  

.. tacn:: expandall  todo
	  
    Expand all possible macros in the sequent. 
      
       



.. tacn:: fa {|@position | @term}
   :name: fa

   TODO



.. tacn:: namelength todo
	  
    Adds the fact that two names have the same
    length. 
      
    Usage: namelength m1, m2  


.. tacn:: rewrite todo
	  
    If t1 = t2, rewrite all occurences of t1 into t2 in the goal.
    Usage: rewrite Hyp Lemma Axiom.
    rewrite Lemma Axiom.
    rewrite Lemma in H. 
      
       

      
Local tactics
~~~~~~~~~~~~~



.. tact:: congruence
   :name: congruence	   

     Attempt to conclude by automated reasoning on message (dis)-equalities.
     Equalities and disequalities are collected from hypotheses, both local 
     and global, after the destruction of conjunctions (but no case analyses 
     are performed to handle conjunctive hypotheses). If the conclusion
     is a message (dis)-equality then it is taken into account as well.

.. tact:: const todo
	  
    Add the `const` tag to a variable. 
      
    Usage: const t  
	    

.. tact:: eqnames todo
	  
    Add index constraints resulting from names equalities, modulo the known
    equalities. 
      
    Usage: eqnames   

.. tact:: eqtrace todo
	  
    Add terms constraints resulting from timestamp and index
    equalities. 
      
    Usage: eqtrace   

.. tact:: executable todo
	  
    Assert that exec@_ implies exec@_ for all previous
    timestamps. 
      
    Usage: executable ts  


.. tact:: project todo
	  
    Turn a goal on a bisystem into one goal for each projection of the
    bisystem. 
      
    Usage: project


.. tact:: rewrite equiv  todo
	  
    Use an equivalence to rewrite a reachability goal. 


.. tact:: slowsmt todo
	  
    Version of smt tactic with higher time limit. 
      
    Usage: slowsmt   

.. tact:: smt todo
	  
    Tries to discharge goal using an SMT solver. 
      
    Usage: smt   

.. tact:: subst todo
	  
    If i = t where i is a variable, substitute all occurences of i by t and
    remove i from the context
    variables. 
      
    Usages: subst idx1, idx2
            subst ts1, ts2
            subst m1, m2  

    
    
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

	


.. tace:: deduce todo
	  
    `deduce i` removes the ith element from the biframe when it can be
    computed from the rest of the biframe.
    `deduce` try to deduce the biframe with the first equivalence in the
    hypotheses it finds. 
      
    Usage: deduce [i]  


.. tace:: diffeq todo
	  
    Closes a reflexive goal up to equality 
      
    Usage: diffeq       
	    


Cryptographic tactics
---------------------

Common tactics
~~~~~~~~~~~~~~


.. tacn:: fresh @position
   :name: fresh

   TODO

   
Local tactics
~~~~~~~~~~~~~


.. tact:: cdh todo
	  
    Usage: cdh H, g.
    Applies the CDH assumption (including squareCDH) on H using generator
    g. 
      
       

.. tact:: collision  todo
	  
    Collects all equalities between hashes occurring at toplevel in message
    hypotheses, and adds the equalities between messages that have the same
    hash with the same valid key. 
      
    Usage: collision [H]  


.. tact:: euf todo
	  
    Apply the euf axiom to the given hypothesis name. 
      
       

.. tact:: gdh todo
	  
    Usage: gdh H, g.
    Applies the GDH assumption (including squareGDH) on H with generator
    g. 
      
       

.. tact:: intctxt todo
	  
    Apply the INTCTXT axiom to the given hypothesis name. 
      
       


Global tactics
~~~~~~~~~~~~~~


.. tace:: cca1 todo
	  
    Apply the cca1 axiom on all instances of a ciphertext. 
      
       
.. tace:: ddh todo
	  
    Closes the current system, if it is an instance of a context of
    ddh. 
      
    Usage: ddh H1, H2, H3, H4  

.. tace:: enckp todo
	  
    Keyprivacy changes the key in some encryption
    subterm. 
      
    Usage: enckp i, [m1], [m2]  


.. tacn:: prf @position
   :name: prf

   TODO why optional message in Squirrel tactic; also fix help in tool    
       

.. tace:: xor todo
	  
    Removes biterm (n(i0,...,ik) XOR t) if n(i0,...,ik) is
    fresh. 
      
    Usage: xor i, [m1], [m2]  

	
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
    
