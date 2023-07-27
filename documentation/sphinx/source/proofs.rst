.. _section-proofs:

.. How to write proofs in Squirrel

------
Proofs
------

The proof of a goal is given after the goal
between the :g:`Proof` and :g:`Qed` markers.
It consists in a list of tactics. The invokation of each
tactic modifies the proof state, which contains a list of goals to prove.
Initially, the proof state consists of a single goal, as declared by the
user. Each tactic then reduces the first goal of the proof state to
an arbitrary number of new subgoals. When no goal is left, the proof
is completed and :g:`Qed` can be used.

Generalities
============

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


Automatic simplifications
-------------------------

.. todo:: document what is done implicitly after each tactic invokation,
	  clarify that this is not the same as calling the `simpl` tactic.

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

TODO

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


Logical tactics
---------------

Common tactics
~~~~~~~~~~~~~~

.. tacn:: admit {? @position}
   :name: admit     

    Admit the current goal, or admit an element from a 
    biframe. 


.. tacn:: assumption (local+global)
   :name: assump
      
    Concludes if the goal or false appears in the
    hypotheses. 

    
    Usages: assumption 
    assumption H  


.. tacn:: case (local+global)
	  
    Perform a case analysis. 
      
    Usages: case ts
            case H
            case m  

.. tacn:: clear (local+global)
	  
    Clear an hypothesis. 
      
     
.. tacn:: dependent induction  (local+global)
	  
    Apply the induction scheme to the
    conclusion. 
      
    Usage: dependent induction   

.. tacn:: destruct  (local+global)
	  
    Destruct an hypothesis. An optional And/Or introduction pattern can be
    given.
    
    Usages: destruct H.
            destruct H as [A | [B C]] 
      
       

.. tacn:: exists  (local+global)
	  
    Introduce the existentially quantified variables in the conclusion of the
    judgment, using the arguments as existential witnesses.
    
    Usage: exists v1, v2, ... 
      
       

.. tacn:: generalize (local+global)
	  
    Generalize the goal on some terms 
      
       

.. tacn:: generalize dependent  (local+global)
	  
    Generalize the goal and hypotheses on some terms 
      
       

.. tacn:: have (local+global)
	  
    Add a new hypothesis. 
      
       

.. tacn:: help
	  
    Display all available commands.
    
    Usages: help
            help tacname
            help concise 
      
       

.. tacn:: id (local+global)
	  
    Identity. 
      
    Usage: id   

.. tacn:: induction (local+global)
	  
    Apply the induction scheme to the conclusion. 
      
    Usage: induction   

.. tacn:: intro (local+global)
	  
    Introduce topmost connectives of conclusion formula, when it can be done
    in an invertible, nonbranching fashion.
    
    Usage: intro a b _ c * 
      
       

.. tacn:: left  (local+global)
	  
    Reduce a goal with a disjunction conclusion into the goal where the
    conclusion has been replaced with the first disjunct. 
      
    Usage: left   

.. tacn:: lemmas (local+global)
	  
    Print all proved lemmas. 
      
    Usage: lemmas   




.. tacn:: print  (local+global)
	  
    Shows def of given symbol or system. By default shows current
    system. 
      
    Usage: print   

.. tacn:: prof
	  
    Print profiling information. 
      
    Usage: prof   



.. tacn:: reduce {? @simpl_flags}

     Reduce all terms in a subgoal, working on both hypotheses and conclusion.
     
     This tactic always succeeds, replacing the initial subgoal with a
     unique subgoal (which may be identical to the initial one).

     The tactic uses the :ref:`reduction engine <reduction>`
     with the provided flags.


     
.. tacn:: remember (local+global)
	  
    substitute a term by a fresh variable 
      
       

.. tacn:: revert (local+global)
	  
    Take an hypothesis H, and turns the conclusion C into the implication H
    => C. 
      
       

.. tacn:: right  (local+global)
	  
    Reduce a goal with a disjunction conclusion into the goal where the
    conclusion has been replaced with the second disjunct. 
      
    Usage: right   

.. tacn:: search  (local+global)
	  
    Search lemmas containing a given pattern. 
      
    Usage: search   

.. tacn:: show  (local+global)
	  
    Print the messages given as argument. Can be used to print the values
    matching a pattern. 
      
    Usage: show m  

.. tacn:: split  (local+global)
	  
    Split a conjunction conclusion, creating one subgoal per
    conjunct. 
      
    Usage: split   

       
.. tacn:: use  (local+global)
	  
    Instantiate a lemma or hypothesis on some arguments.
    
    Usage:
    use H with v1, ..., vn.
    use H with v1 as intro_pat. 
      

      
Local tactics
~~~~~~~~~~~~~



.. tact:: true (lowtactic)
	  
    Solves a goal when the conclusion is true. 
      
    Usage: true   

      
Global tactics
~~~~~~~~~~~~~~


.. tace:: byequiv (equiv)
	  
    transform an equivalence goal into a reachability
    goal. 
      
    Usage: byequiv   
  

.. tace:: constseq (equiv)
	  
    simplifies a constant sequence 
      
       

.. tace:: enrich (equiv)
	  
    Enrich the goal with the given term. 
      
    Usages: enrich m
            enrich f  


.. tace:: localize  (global)
	  
    Change a global hypothesis containing a reachability formula to a local
    hypothesis. 
      
    Usage: localize H1, H2  


.. tace:: memseq (equiv)
	  
    prove that an biframe element appears in a sequence of the biframe. 
      
       

.. tace:: refl (equiv)
	  
    Closes a reflexive goal. 
      
    Usage: refl   


.. tace:: splitseq (equiv)
	  
    splits a sequence according to some boolean 
      
       

.. tace:: sym (equiv)
	  
    Prove an equivalence by symmetry. 
      
    Usage: sym   

.. tace:: trans (equiv)
	  
    Prove an equivalence by transitivity. 
      

Structural tactics
------------------


Common tactics
~~~~~~~~~~~~~~

      
.. tacn:: apply  (local+global)
	  
    Matches the goal with the conclusion of the formula F provided (F can be
    an hypothesis, a lemma, an axiom, or a proof term), trying to instantiate
    F variables by matching. Creates one subgoal for each premises of
    F.
    Usage
    apply H.
    apply lemma.
    apply axiom. 
      
       


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


.. tacn:: autosimpl (local+global)
	  
    Simplify a goal, without closing it. Automatically called after each
    tactic. 
      
    Usage: autosimpl   


.. tacn:: constraints

     Attempt to conclude by automated reasoning on trace literals.
     Literals are collected from hypotheses, both local and global,
     after the destruction of conjunctions (but no case analyses are
     performed to handle conjunctive hypotheses). If the conclusion
     is a trace literal then it is taken into account as well.

    
.. tacn:: depends  (local+global)
	  
    If the second action depends on the first action, and if the second
    action happened, add the corresponding timestamp
    inequality. 
      
    Usage: depends ts1, ts2  


.. tacn:: expand  (local+global)
	  
    Expand all occurences of the given macro inside the
    goal. 
      
    Usages: expand H
            expand m
            expand f  

.. tacn:: expandall  (local+global)
	  
    Expand all possible macros in the sequent. 
      
       



.. tacn:: fa {@position | @term}
   :name: fa

   TODO



.. tacn:: namelength (local+global)
	  
    Adds the fact that two names have the same
    length. 
      
    Usage: namelength m1, m2  


.. tacn:: rewrite (local+global)
	  
    If t1 = t2, rewrite all occurences of t1 into t2 in the goal.
    Usage: rewrite Hyp Lemma Axiom.
    rewrite Lemma Axiom.
    rewrite Lemma in H. 
      
       

       


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

     
      
Local tactics
~~~~~~~~~~~~~



.. tact:: congruence
   :name: congruence	   

     Attempt to conclude by automated reasoning on message (dis)-equalities.
     Equalities and disequalities are collected from hypotheses, both local 
     and global, after the destruction of conjunctions (but no case analyses 
     are performed to handle conjunctive hypotheses). If the conclusion
     is a message (dis)-equality then it is taken into account as well.

.. tact:: const (local)
	  
    Add the `const` tag to a variable. 
      
    Usage: const t  
	    

.. tact:: eqnames (local)
	  
    Add index constraints resulting from names equalities, modulo the known
    equalities. 
      
    Usage: eqnames   

.. tact:: eqtrace (local)
	  
    Add terms constraints resulting from timestamp and index
    equalities. 
      
    Usage: eqtrace   

.. tact:: executable (local)
	  
    Assert that exec@_ implies exec@_ for all previous
    timestamps. 
      
    Usage: executable ts  


.. tact:: project (local)
	  
    Turn a goal on a bisystem into one goal for each projection of the
    bisystem. 
      
    Usage: project


.. tact:: rewrite equiv  (local)
	  
    Use an equivalence to rewrite a reachability goal. 


.. tact:: slowsmt (local)
	  
    Version of smt tactic with higher time limit. 
      
    Usage: slowsmt   

.. tact:: smt (local)
	  
    Tries to discharge goal using an SMT solver. 
      
    Usage: smt   

.. tact:: subst (local)
	  
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

	


.. tace:: deduce (equiv)
	  
    `deduce i` removes the ith element from the biframe when it can be
    computed from the rest of the biframe.
    `deduce` try to deduce the biframe with the first equivalence in the
    hypotheses it finds. 
      
    Usage: deduce [i]  


.. tace:: diffeq (equiv)
	  
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


.. tact:: cdh (local)
	  
    Usage: cdh H, g.
    Applies the CDH assumption (including squareCDH) on H using generator
    g. 
      
       

.. tact:: collision  (local)
	  
    Collects all equalities between hashes occurring at toplevel in message
    hypotheses, and adds the equalities between messages that have the same
    hash with the same valid key. 
      
    Usage: collision [H]  


.. tact:: euf (local)
	  
    Apply the euf axiom to the given hypothesis name. 
      
       

.. tact:: gdh (local)
	  
    Usage: gdh H, g.
    Applies the GDH assumption (including squareGDH) on H with generator
    g. 
      
       

.. tact:: intctxt (local)
	  
    Apply the INTCTXT axiom to the given hypothesis name. 
      
       


Global tactics
~~~~~~~~~~~~~~


.. tace:: cca1 (equiv)
	  
    Apply the cca1 axiom on all instances of a ciphertext. 
      
       
.. tace:: ddh (equiv)
	  
    Closes the current system, if it is an instance of a context of
    ddh. 
      
    Usage: ddh H1, H2, H3, H4  

.. tace:: enckp (equiv)
	  
    Keyprivacy changes the key in some encryption
    subterm. 
      
    Usage: enckp i, [m1], [m2]  


.. tacn:: prf @position
   :name: prf

   TODO why optional message in Squirrel tactic; also fix help in tool    
       

.. tace:: xor (equiv)
	  
    Removes biterm (n(i0,...,ik) XOR t) if n(i0,...,ik) is
    fresh. 
      
    Usage: xor i, [m1], [m2]  

	
