.. _section-declarations:

============
Declarations
============

We details here how to define the multiple constructs over which the
logic will reason.


Term constructs
===============
        
Names
-----

:gdef:`Names <name>` model values that are sampled uniformaly at random whihin a :term:`large` type. They are drawn independantly from 

.. prodn::
   name_id ::= @identifier
   name ::= name @name_id : [(@index * ... * @index) ->] @base_type

.. note::
   Since :cite:`bkl23hal`, our terms are not necessarily
   computable in polynomial time by probabilistic Turing machines.  An
   example of a non-PTIME term is ``forall (x:message), x = f(x)``
   which tests whether ``f`` is idempotent, something that is not
   necessarily computable even when ``f`` is PTIME.


Abstract symbols
----------------

:gdef:`Abstract functions<abstract_fun>` are free function symbols,
that model function over which no assumptions are made by
default, except that they are deterministic polynomial time computations.


.. prodn::
   fun_id ::= @identifier
   tvar_args ::=  [{+ @type_variable }]
   function ::= abstract {? @tvar_args} @fun_id : @type

Function symbols support polymorphisms through the optional :n:`@type_variable`.
The behaviour of functions symbols can be defined through :term:`axioms <axiom>`. 

.. note:: 
   Many builtins function symbols heavily rely on the
   polymoprhisms, allowing for instance to have a common equality
   symbol for all types :g:`abstract (=) ['a] : 'a -> 'a -> bool`.
   When declaring :term:`axioms <axiom>` over such function symbols
   can easily lead to contradictions, as for instance one may assume
   that all types contain a single element, or are infinite, ....

Builtins
++++++++

Several function symbols are builtin in Squirrel, along with their
axiomatizations. This notably includes the logical connectors for a
:term:`local formula`.


.. todo::
   what do we have here? if then else, pair, fst, snd, len? 


Cryptographic functions
-----------------------

Squirrel allows to declare functions modeling classical cryptographic with:

.. prodn::
   crypto_decl ::= hash @fun_id 
   | signature @fun_id, @fun_id, @fun_id
   | aenc @fun_id, @fun_id, @fun_id
   | senc @fun_id, @fun_id, @fun_id
   | {| ddh | cdh | gdh } @fun_id, @fun_id where group:@base_type exponents:@base_type

where:

* :g:`hash h` declares a keyed hash function :g:`h(m,k)` satisfying PRF and known key collision resistance.
* :g:`signature sig,ver,pk` declares an unforgeable (EUF-CMA) signature with the equation :g:`ver(sig(m,sk),m,pk(sk))=true`.
* :g:`aenc enc,dec,pk` declares an IND-CCA2 asymmetric encryption with the equation :g:`dec(enc(m,pk(sk)),sk)=m`.
* :g:`senc enc,dec` declares an IND-CCA2 symmetric encryption with the equation :g:`dec(enc(m,sk),sk)=m`. 
* :g:`ddh g, (^) where group:message exponents:message.` declares a group with generator :g:`g`, exponentation function :g:`^` over the given types. Dedicate types for exponents and messages are often defined.  The group satisfies DDH when declared with :g:`ddh`, CDH with :g:`cdh`, and gapDH with :g:`gdh`.


Operators
---------

:gdef:`Operators <operator>` are function symbols defined with a
concrete computation corresponding to their evluation.

.. prodn::
   op_id ::= @identifier
   operator ::= op @op_id {? @tvar_args } {+ ({+, @variable} : @type) } : @type = @term
 
As recursion is not yet supported, this is in fact currently syntact
sugar for declaring an :term:`abstract function <abstract_fun>` symbol along with an :term:`axiom` stating
the equation giving its defintion.

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
 * todos

  
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

An :gdef:`axiom` defines...

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
