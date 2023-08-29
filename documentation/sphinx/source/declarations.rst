.. _section-declarations:

============
Declarations
============

We details here how to define the multiple symbols and objects used by
the logic.


Term symbols
============
        
Names
-----

Names are used to model random samplings.

.. prodn::
   name_id ::= @identifier

.. decl:: name @name_id : {? @type ->} @type

  A name declaration :n:`name @name_id : {? @type__i ->} @type__s` adds a
  new name symbol :n:`@name_id` optionally indexed by :n:`@type__i` and
  sampling values of type :n:`@type__s`.
  
  It is required that the indexing type :n:`@type__i` is a
  :term:`finite` type, but there are no restrictions over sampling type
  :n:`@type__s`. 
   
  The sampling *distribution* used over the sampling type :n:`@type__s`
  is usually arbitrary --- though it can be restricted using 
  :term:`type tags<type tag>` --- except for the
  :g:`message` type, over which sampling is done uniformly at
  random over bit-strings of length exactly :math:`\eta`.

Two distinct applied name symbols, or the same name symbol applied to
two different index values, denote **independent** random samplings.

.. note::
   Since :cite:`bkl23hal`, terms do not necessarily represents
   computable values.
   An example of a non-PTIME term is :g:`forall(x:message), x = f(x)`
   which tests whether :g:`f` is idempotent, something that is not
   necessarily computable even when :g:`f` is.

.. todo::
   Adrien: this last note is out-of-place.

Abstract function
-----------------

:gdef:`Abstract functions<abstract_fun>` are model
functions over which no assumptions are made, apart from the fact that
they are *deterministic* and *polynomial-time computable*.
If needed, their behaviour can be restricted further through :term:`axioms
<axiom>`.

.. prodn::
   fun_id ::= @identifier | (@infix_op)

.. decl:: abstract @fun_id {? [@tvar_params]} : @type

  Declares a deterministic and polynomial-type computable abstract
  function named :n:`@fun_id` with type :n:`@type`.

  The function can be :ref:`polymorphic<section-polymorphism>` 
  through the optional :n:`@tvar_params` type variable parameters.

An abstract function must be used in prefix notation if its name is an
:n:`@identifier`, and in infix notation if its name is an
:n:`@infix_op` (note the parenthesis around :n:`(@infix_op)` in the
declaration).

.. example:: 
             
   Equality is defined in Squirrel as the polymorphic abstract function 

   .. squirreldoc::
      abstract (=) ['a] : 'a -> 'a -> bool
..
  Adrien: I removed the sentence below, which seemed too specific and not
  clear enough.
  
  When declaring :term:`axioms <axiom>` over such function symbols
  can easily lead to contradictions, as for instance one may assume
  that all types contain a single element, or are infinite, ....

Built-ins
+++++++++

Squirrel features several :gdef:`built-in` function symbols which built-in axiomatizations.

* :n:`if @term then @term else @term`,
  used in :term:`terms <term>`, is from
  a theoretical point a built-in.
* :n:`happens(@term)`, :n:`pred(@term)` and :n:`init` are three
  function symbols dedicated to the :term:`timestamp` type. Each model
  instantiates the set of timestamps by specifying which one happens
  on the given trace, and for all the one that happen, their total
  ordering, :n:`init` refering to a fixed first timestamp and
  :n:`pred` being the predecessor function.
* The boolean connectors of :term:`local formulas<local formula>` are built-ins:
  :n:`true`, :n:`false`, :n:`&&`, :n:`||`, :n:`=>`, :n:`<=>` and :n:`not`.
* Comparison functions :n:`=`, :n:`<>`, :n:`<=`, :n:`<`, :n:`>=` and :n:`>`.
* A witness function :n:`witness`.
* A dedicated :n:`xor` symbol along with its :n:`zero`.
* A convertion function from :g:`bool` to :g:`message`, :n:`of_bool`.
* Utility constants for failure, :n:`fail`, and an empty message, :n:`empty`.
* The successor function over natural numbers `succ`.
* Pairing and projection functions, :n:`pair` (also denoted :n:`<x,y>`) with :n:`fst` and :n:`snd`.
* A length function for the number of bits in messages, :n:`len`, as well as a function producing a bitstring of zeroes of the same length as the input, :n:`zeroes`.
   

Cryptographic functions
-----------------------

Squirrel allows to declare functions modeling standard
:gdef:`cryptographic functions <cryptographic function>` with:

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
* :g:`ddh g, (^) where group:message exponents:message.` declares a
  group with generator :g:`g` and exponentation :g:`(^)`. The group
  must satisfy the DDH assumption when declared with :g:`ddh`, the CDH assumption with
  :g:`cdh`, and the GapDH assumption with :g:`gdh`.


Operators
---------

Operators are function symbols with a concrete user-defined semantics.
An operator's semantics must be *deterministic*.

.. prodn::
   op_id ::= @identifier | (@infix_op)

.. decl:: operator ::= op @op_id {? [@tvar_params] } @binders {? : @type } = @term

   Declares an operator named :n:`@op_id`, arguments :n:`@binders` and
   returning :n:`@term`. 

   The return type :n:`@type` can be provided, or left to be
   automatically inferred by Squirrel.
  
   Operator declarations can be :ref:`polymorphic<section-polymorphism>` through 
   the optional :n:`@tvar_params` type variable parameters.

   An operator declaration *fails* if Squirrel cannot syntactically check
   that its body represents a deterministic value.

An operator must be used in prefix notation if its name is an
:n:`@identifier`, and in infix notation if its name is an
:n:`@infix_op` (note the parenthesis around :n:`(@infix_op)` in the
declaration).

..
  As recursion is not yet supported, this is in fact currently syntact
  sugar for declaring an :term:`abstract function <abstract_fun>` symbol along with an :term:`axiom` stating
  the equation giving its defintion.

.. todo::
   Adrien: removed the comment about axiomatization.


.. _section-processes:

Processes
=========

The input language for protocoles relies on a dialect of the applied-pi calculus.


.. _section-channel:

Channels
--------

Communications over the network are performed over public channels, identified by a name.

.. prodn::
   channel_id ::= @identifier

.. decl:: channel @channel_id

   Declares a channel named :n:`@channel_id`.
 
  
.. _section-mutable-state:

Mutable state
-------------

Processes in Squirrel can use mutable states.

.. prodn::
   state_id ::= @identifier

.. decl:: mutable @state_id @binders {? : @type} = @term
  
   Declares a memory cell named :n:`state_id` indexed by arguments
   :n:`@binders` --- which must be of :term:`finite` type --- and initialized
   to :n:`term`.

   The return type :n:`@type` can be provided, or left to be
   automatically inferred by Squirrel.
   
.. example:: State counter
	     
   .. squirreldoc:: 
      mutable counter (i,j,k:index) : message = zero

   declares a set of counter states indexed by :g:`i,j,k`, all initialized 
   to :g:`zero`, i.e. the following formula is valid:
  
   .. squirreldoc::
      forall i j k, counter (i,j,k) @ init = zero`
   
Process declaration
-------------------

The basic process constructs are:

.. prodn::
   basic_process ::= new @name_id | @state[({*, @term})] := @term | out(@channel, @term) | in(@channel, @term)

A basic process can be:

 * The binding of a name with :g:`new name`, which implicitly declares
   a new :decl:`name symbol<name>` indexed by the current replication indices. This
   is syntactic sugar that can be avoided by manually declaring the
   needed name symbols with the appropriate arities before the process
   declaration.
 * The stateful update of a :ref:`memory cell<section-mutable-state>`.
 * An input or an output over a :ref:`channel<section-channel>`.

  
The body of a process is defined with sequential or parallel
composition of basic processes, conditionals, find constructs,
replication or process calls.

..  prodn::
    process_id ::= @identifier
    alias ::= @identifier
    proc ::= @basic_process; @proc
        | @proc | @proc
	| if @term then @proc else @proc
	| try find @binders such that @term in @proc else @proc
	| let @identifier = @term in @proc
	| !_@identifier @proc
	| @process_id[({*, @term})]
	| @alias : @proc

The construct :g:`A : proc` does not have any semantic impact: it is
only used to give an alias to this location in the process.

.. decl:: process @process_id @binders = @proc	
   
   Declares a new process named :n:`@process_id` with arguments :n:`@binders`
   and body :n:`@proc`.


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

Systems are used to declare protocols through set of
actions. A single system can refer to a set of actions, and a system
is usually though of as a set of single systems.

A system a defined by a main process:

.. prodn::
   system_id ::= @identifier

.. decl:: system {? [@system_id]} @process

   As :n:`@process` uses bi-terms, this declares a :gdef:`bi-system`
   comprising a left and right :gdef:`single system`, where the left
   (resp. right) single system is described by the protocol obtained
   by taking the left (resp. right) components of all bi-terms
   appearing in :n:`@process`.

   The system name :n:`@system_id` defaults to :n:`default` when no
   system identifier is specified.

.. example:: System declarations

	     Using the previously defined :n:`Dummy` process, we
	     define a system with :g:`system [myProtocol] Dummy`.
	     Another distinct system could be declared with :g:`system
	     (Dummy | out(c,empty))`, which would this time be named
	     :n:`default`.


.. _section-system-macros:

System-defined macros
+++++++++++++++++++++


Whenever a system is declared, for each action `A[idx]` inside the system with output value `o(x)` and condition `c(x)` where `x` denotes the input of action `A[idx]`, multiple mutually recursive macros are declared:

* :g:`output@A[idx] := o(input@A[idx])`.
* :g:`cond@A[idx] := c(input@A[idx])`.
* :g:`input@A[idx] := att(frame@pred([idx]))`.
* :g:`frame@tau` is equal to :g:`<frame@pred(tau), if cond@tau then output@tau>` if :g:`tau` happens and is not the first timestamp :g:`init`. Otherwise, :g:`frame@tau` is :g:`empty`.
* :g:`exec@tau` is equal to :g:`exec@pred(tau) && cond@tau>` if :g:`tau` happens and is not the first timestamp :g:`init`. Otherwise, :g:`exec@init` is :g:`true`.

System expressions
++++++++++++++++++

.. prodn::
   single_system_expr ::= @system_id/left | @system_id/right

:n:`@system_id/proj` is an unlabeled single system 
representing the left (if :n:`proj = left`) or right (if :n:`proj = right`)
component of the :term:`bi-system` named :n:`@system_id`.


.. prodn::
   system_expr ::= any | @system_id | {*, @single_system_expr}

A :gdef:`multi-system<multi system>` is a finite set of labeled :term:`single systems<single system>`.
Mutli-systems are specified in Squirrel using
:gdef:`system expressions<system expression>`.

* :n:`any` containts all labeled single systems;

* :n:`@system_id` is the bi-system composed of the two single systems
  defined by :n:`@system_id`, implicitely labeled by :n:`left` and
  :n:`right`;

* :n:`@single_system_expr__1,...,@single_system_expr__n` is the multi-system of
  the :n:`n` given single systems implicitely labeled:

  + ε if :n:`n = 1`

  + :n:`left` and :n:`right` if :n:`n = 2`

  + by the :n:`n` first positive integers otherwise

System contexts
+++++++++++++++
  
.. prodn::
   system_context ::= set: @system_expr; equiv:  @system_expr
   | @system_id

A *concrete system context* :g:`set:S; equiv:P` comprises:

* a multi-system specified by :g:`S` used to interpret
  :term:`reachability atoms<reachability atom>`

* a pair of systems (i.e. a mutli-system with two elements) :g:`P`
  used to interpret :term:`equivalence atoms<equivalence atom>`.

A *system context alias* :g:`S` --- where :g:`S` is a
:n:`@system_id` --- is syntactic sugar for :g:`set:S; equiv:S/left,S\right`.


Axioms and Goals
================

Squirrel supports two kinds of :gdef:`goals<goal>` (usually called
*lemmas* in proof-assistants), one for each kind of formulas:
:gdef:`local goals<local goal>` for :term:`local formulas<local formula>` and
:gdef:`global goals<global goal>` for :term:`global formulas<global formula>`.
Similarly, there are local and global of
:gdef:`axioms<axiom>`. The only difference between a goal and an axiom
declaration is that the former creates a proof-obligation that must be
discharged by the user through a :ref:`proof<section-proofs>`.

.. prodn::
   statement_id ::= @identifier 
   local_statement ::= {? [@system_expr] } {| @goal_id | _} {? [@tvar_params]} @binders : @formula
   global_statement ::= {? [@system_context] } {| @goal_id | _} {? [@tvar_params]} @binders : @global_formula
   goal_or_axiom_decl ::= {? local} {| goal | axiom } @local_statement
                      | global {| goal | axiom} @global_statement


Local and global statements can be
:ref:`polymorphic<section-polymorphism>` through the optional
:n:`@tvar_params` type variable parameters.

Unnamed (local and global) statements can be declared using an
underscore :g:`_` instead of a statement identifier
:g:`@statement_id`.
                      
Local statements
----------------
   
:n:`{? [@system_expr] } @goal_id [@tvar_params] @binders : @formula`

is a local statement over the systems :n:`[@system_expr]` (which
defaults to system expression :n:`[default]`) named :n:`@goal_id`.  This
statements holds if, for any value of the type parameters
:n:`@tvar_params`, the local formula :n:`forall @binders, @formula`
holds.

.. example:: Some axioms and goals
	     
   .. squirreldoc::
      axiom [any] fail_not_pair (x,y:message): <x,y> <> fail

   states that in any system, a pair has a negligible probability of
   being equal to the constant :g:`fail`.

   .. squirreldoc::
      axiom no_repeat t t' : happens(t,t') => t <> t' => input@t <> input@t'

   states that in system :g:`[default]`, the adversary never sent the message twice.

   .. squirreldoc::
      goal [myProtocol/left] _ : cond@A2 => input@A1 = ok

   is an unnamed local goal stating that a action :g:`A2` is executed
   only if the adversary sent the message :g:`ok` at time-point `A1`

Global statements
-----------------

:n:`{? [@system_context] } @goal_id [@tvar_params] @binders : @global_formula`

is a global statement over the system context :n:`[@system_context]` (which
defaults to system context :n:`[default]`) named :n:`@goal_id`.  This
statements holds if, for any value of the type parameters
:n:`@tvar_params`, the global formula :n:`Forall @binders, @global_formula`
holds.

.. example:: 

  .. squirreldoc::
     global goal [myProtocol] obs_equiv (t:timestamp[const]) : [happens(t)] -> equiv(frame@t)

  states that protocol :g:`myProtocol` (seen as a bi-process) is observationally equivalent.
  
  .. squirreldoc::
     global goal [set: real/left; equiv: real/left,ideal/right] ideal_real_equiv :
       Forall (tau:timestamp[const]), [happens(tau)] -> equiv(frame@tau)

  states that protocols :g:`real/left` and :g:`ideal/right` are observationally equivalent.
