.. _section-declarations:

============
Declarations
============

Term constructs
===============


Abstract symbols
----------------

:gdef:`Abstract functions<abstract_fun>` TODO

Function symbols are deterministic polynomial time.

Cryptographic functions
-----------------------




Operators
---------

:gdef:`Operators <operator>`

         
Names
-----

TODO :gdef:`names <name>`

.. prodn::
   name_id ::= @identifier
   name ::= name @name_id : [(@index * ... * @index) ->] @type

.. note::
  Unlike in the original BC logic and the meta-logic that was used at first
  in Squirrel, our terms are not necessarily computable in polynomial time
  by probabilistic Turing machines.
  An example of a non-PTIME term is ``forall (x:message), x = f(x)``
  which tests whether ``f`` is idempotent, something that is not
  necessarily computable even when ``f`` is PTIME.

  TODO citations

Macros
------

TODO :gdef:`macros <macro>`



.. _section-processes:

Processes
=========

The input language for protocoles relies on a dialect of the applied-pi calculus. Communications over the network are performed over public channels, identified by a name.

.. prodn::
   channel_id ::= @identifier
   channel ::= channel @channel_id

Processes are allowed to manipulate states, defined with an identifier, a replication indices, the type of term stored inside the state and the initial value of the state:

.. prodn::
   state_id ::= @identifier
   state ::= mutable @state_id[({*, @binders})] : @type = @term

.. todo::
  Charlie: I'm not sure how to restrict the set of binders to binders of type index.

The basic commands are:

.. prodn::
   command ::= new @name_id | @state[({*, @term})] := @term | out(@channel, @term) | in(@channel, @term)

A command can be:
 * the binding of a name with :g:`new name`, which implicitly declares a new name based on the current replication indices. This is strictly syntactic sugar that can be avoided by explicitely declaring all names at the begining    
   
The body of a process is defined with sequential or parallel composition of commands,conditionals, find constructs, replication or process calls.

..  prodn::
    process_id ::= @identifier
    alias ::= @identifier
    proc ::= @command; @proc
        | @proc | @proc
	| if @term then @proc else @proc
	| try find @binders such that @term in @proc else @proc
	| let @identifier = @term in @proc
	| !_@identifier @proc
	| @process_id[({*, @term})]
	| @alias : @proc
    process_decl ::= process @process_id[({*, @binders})] = @proc	

The construct :g:`A : proc` does not have any impact on the semantics of the model: it is only used to give an alias to this location in the process.	



Systems
-------

:gdef:`systems <system>` TODO

.. prodn::
  system_id ::= identifier | identifier / identifier
  system_expr ::= {| any | {+, @system_id} }

TODO expr and set expressions



Finally, a system is defined by a main process:

.. prodn::
   system_decl ::= system [@system_id] @process


.. todo::
   - the implicit declaration of macros,
   - the role of diff operators


Logics
======

Axioms
------

Goals
-----

A :gdef:`goal <goal>` defines a new formula to be proved. It can either be a :gdef:`local goal <local goal>` or a :gdef:`global goal <global goal>`, respectively corresponding to defining as a goal a :term:`local formula <local formula>` or a :term:`global formula <global formula>`.

.. prodn::
  goal ::= local_goal
  local_goal ::= {? local } goal {? @system_expr } {| @identifier | _ } @parameters : @formula
  global_goal ::= global goal {? @system_expr } {| @identifier | _ } @parameters : @global_formula

.. example:: Unnamed local goal

  :g:`goal [myProtocol/left] _ : cond@A2 => input@A1 = ok.`

.. example:: Global goal expressing observational equivalence

  :g:`global goal [myProtocol] obs_equiv (t:timestamp) : happens(t) => equiv(frame@t).`
