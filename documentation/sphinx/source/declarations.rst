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
axiomatizations.


* :n:`diff(@term,@term)` and :n:`if @term then @term else @term`,
  introduced to describe the syntax of :term:`terms <term>`, are from
  a theoretical point abstract function builtins.
* :n:`happens(@term)`, :n:`pred(@term)` and :n:`init` are three
  function symbols dedicated to the :term:`timestamp` type. Each model
  instantiates the set of timestamps by specifying which one happens
  on the given trace, and for all the one that happen, their total
  ordering, :n:`init` refering to a fixed first timestamp and
  :n:`pred` being the predecessor function.
* The connector for a :term:`local formula` are in fact a builtin,
  with :n:`true`, :n:`false`, :n:`&&`, :n:`||`, :n:`=>`, :n:`<=>`) and :n:`not`.
* Comparison operators :n:`=`, :n:`<>`, :n:`<=`, :n:`<`, :n:`>=` and :n:`>`.
* A witness function :n:`witness`.
* A dedicated :n:`xor` symbol along with its :n:`zero`. (this should be deprecated at some point in favour of a :term:`cryptographic function` declaration).  
* A convertion function from :g:`bool` to :g:`message`, :n:`of_bool`.
* Utility constants for failure, :n:`fail`, and an empty message, :n:`empty`.
* The successor function over natural numbers `succ`.
* Pairing and projection functions, :n:`pair` (also denoted :n:`<x,y>`) with :n:`fst` and :n:`snd`.
* A length function for the number of bits in messages, :n:`len`, as well as a function producing a bitstring of zeroes of the same length as the input, :n:`zeroes`.



Cryptographic functions
-----------------------

Squirrel allows to declare functions modeling classical :gdef:`cryptographic functions <cryptographic function>` with:

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


:gdef:`Macros <macro>` are a very specific kind of recursive operators
only taking timestamps as input. They cannot be user-defined now, and
a dedicated set of macros can only be defined through the definition
of a system, see the :ref:`system-defined macro section
<section-system-macros>`.

Macros can occur in terms, and their syntax is as follows:

.. prodn::
   macro_id ::= @identifier
   macro ::= @macro_id@@term

The syntax :g:`macro@ts` is intuitively a shortcut for :g:`macro(ts)`, and the argument passed my be of type :g:`timestamp`.

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


Actions
-------

Squirrel only manipulates set of actions, to which protocoles as
processes are translated. An action intuitively an atomtic step of a
protocol, where upon receiving an input from the attacker, a condition
is checked and if it holds an output is given back to the
attacker. Actions cannot be directly specified and can only be
declared via processes.


There are identified by an action identifier:

.. prodn::
   action_id ::= @identifier

When translating processes, names are automatically given to actions. Alternatively, they can be specified by an :n:`@alias`.

An action is defined by an action identifier :n:`@action_id`, a set of
:g:`index` variables for the replications, and :g:`message` variable
for the input, and a term of type :g:`bool` for its condition and a term of
type :g:`message` for its output, where the free variables in the two terms
are only the replication and input variables.



Systems
-------

:gdef:`Systems <system>` are used to declare protocols through set of actions. A system can either refer to a set of actions, or to a set of protocols, and thus a set of set of actions.

A system a defined by a main process:

.. prodn::
   system_id ::= identifier
   system_decl ::= system [@system_id] @process

As processes are defined over bi-terms, we in fact declare here a bi-system, refering to the left and right protocols made up when projecting on the left or the righ the bi-terms.

Multi-systems can be refereed to using system expressions:

.. prodn::
   system_expr ::= {| any | {+, {| @system_id | @system_id/left | @system_id/right } } }


.. _section-system-macros:

System-defined Macros
+++++++++++++++++++++


Whenever a system is declared, for each action `A[idx]` inside the system with output value `o(x)` and condition `c(x)` where `x` denotes the input of action `A[idx]`, multiple mutually recursive macros are declared:

* :g:`output@A[idx] := o(input@A[idx])`.
* :g:`cond@A[idx] := c(input@A[idx])`.
* :g:`input@A[idx] := att(frame@pred([idx]))`.
* :g:`frame@tau` is equal to :g:`<frame@pred(tau), if cond@tau then output@tau>` if :g:`tau` happens and is not the first timestamp :g:`init`. Otherwise, :g:`frame@tau` is :g:`empty`.
* :g:`exec@tau` is equal to :g:`exec@pred(tau) && cond@tau>` if :g:`tau` happens and is not the first timestamp :g:`init`. Otherwise, :g:`exec@init` is :g:`true`.

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
