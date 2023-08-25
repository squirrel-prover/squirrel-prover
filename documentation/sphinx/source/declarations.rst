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
   parameters ::= {+ ({+, @variable} : @type) }
   operator ::= op @op_id {? @tvar_args } {? parameters } : @type = @term
 
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
   state ::= mutable @state_id {? ({+, var@} : index) } : @type = @term

.. example:: State counter
	     
   With :g:`mutable counter (i,j,k:index) : message = zero.`
   we declare a set of counter states, all initialized to zero.

The basic commands are:

.. prodn::
   command ::= new @name_id | @state[({*, @term})] := @term | out(@channel, @term) | in(@channel, @term)

A command can be:

 * The binding of a name with :g:`new name`, which implicitly declares a new name based on the current replication indices. This is strictly syntactic sugar that can be avoided by explicitely declaring all names at the begining.
 * The update of a state cell.
 * An input or an output over some channel.

  
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


.. example:: Actions corresponding to process definition

   Consider the following Squirrel code.
	     
   .. squirreldoc::
      abstract one:message.
      channel c.

      process Dummy =
             (!_i (in(c,x);
                  if x=zero then
		     A: out(c,zero)
		  else
		     B: out(c,x)
		  )   
              | 
	        in(c,x); out(c,empty)).
	
   It roduces a set of three actions:
   
   * action :n:`A[i]`, with input variable x, condition `x=zero` and output `zero`;
   * action :n:`B[i]`,  with input variable x, condition `x<>zero` and output `x`;
   * and action :n:`A1` (with automatic naming), condition `true` and output `empty`.  

Systems
-------

:gdef:`Systems <system>` are used to declare protocols through set of actions. A system can either refer to a set of actions, or to a set of protocols, and thus a set of set of actions.

A system a defined by a main process:

.. prodn::
   system_id ::= identifier
   system_decl ::= system {? [@system_id]} @process

As processes are defined over bi-terms, we in fact declare here a :gdef:`bi-system`, refering to the left and right protocols made up when projecting on the left or the righ the bi-terms. If no system identifier is specified, the :n:`default` name is used.

.. example:: System declarations

	     Using the previously defined :n:`Dummy` process, we
	     define a system with :g:`system [myProtocol] Dummy`.
	     Another distinct system could be declared with :g:`system
	     (Dummy | out(c,empty))`, which would this time be named
	     :n:`default`.

Systems can be refereed to, notably in proof goals and axioms, using system expressions:

.. prodn::
   single_expr ::= @system_id/left | @system_id/right
   pair_expr ::= @system_id | @single_expr, @single_expr
   system_expr ::= any | pair_expr 


.. _section-system-macros:

System-defined Macros
+++++++++++++++++++++


Whenever a system is declared, for each action `A[idx]` inside the system with output value `o(x)` and condition `c(x)` where `x` denotes the input of action `A[idx]`, multiple mutually recursive macros are declared:

* :g:`output@A[idx] := o(input@A[idx])`.
* :g:`cond@A[idx] := c(input@A[idx])`.
* :g:`input@A[idx] := att(frame@pred([idx]))`.
* :g:`frame@tau` is equal to :g:`<frame@pred(tau), if cond@tau then output@tau>` if :g:`tau` happens and is not the first timestamp :g:`init`. Otherwise, :g:`frame@tau` is :g:`empty`.
* :g:`exec@tau` is equal to :g:`exec@pred(tau) && cond@tau>` if :g:`tau` happens and is not the first timestamp :g:`init`. Otherwise, :g:`exec@init` is :g:`true`.


Logics
======

Axioms
------

An :gdef:`axiom` defines a :term:`local formula` as true over the corresponding system (over system :n:`default` by default).

.. prodn::
   axiom_id ::= identifier
   axiom_decl ::= axiom  {? @system_expr } @axiom_id {? @parameters } : @formula.


.. example:: Basic axiom
	     
	     The following line declares that in system :n:`default,` the constant
	     :n:`fail` cannot be equal to any pair: :g:`axiom fail_not_pair
	     (x,y:message): fail <> <x,y>`.

   
   
Goals
-----

A :gdef:`goal <goal>` defines a new formula to be proved. It can either be a :gdef:`local goal <local goal>` or a :gdef:`global goal <global goal>`, respectively corresponding to defining as a goal a :term:`local formula <local formula>` or a :term:`global formula <global formula>`.

.. prodn::
  goal ::= local_goal
  local_goal ::= {? local } goal {? [@system_expr] } {| @identifier | _ } @parameters : @formula
  
.. example:: Unnamed local goal

  :g:`goal [myProtocol/left] _ : cond@A2 => input@A1 = ok.`



A global formula can contain both equivalence predicate as well as local formulas. By default, if a system is specified, both equivalence predicates and local predicates will be instantied in the global system. It is possible to refine this using a :gdef:`global system declaration`.

.. prodn::
   global_decl ::= [set: @system_expr; equiv:  @system_expr]
   global_goal ::= global goal {? {| [@system_expr] | @global_decl } } {| @identifier | _ } @parameters : @global_formula

The system specified in the :g:`set:` will then be the system attached to all the local formulas whitin the global goal and the :g:`equiv` system used for all the :g:`equiv` statements.


.. example:: Global goal expressing observational equivalence

  :g:`global goal [myProtocol] obs_equiv (t:timestamp) : [happens(t)] -> equiv(frame@t).`


.. example:: Global goal expressing a transitivity
	     
    :g:`global goal [set: real/left; equiv: real/left,ideal/right] ideal_real : Forall (tau:timestamp[const]),  [happens(tau)] -> equiv(frame@tau)`
