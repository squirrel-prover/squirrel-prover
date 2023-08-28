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

:gdef:`Names<name>` model values that are sampled uniformaly at
random. Distinct names represent independant random samplings.

.. prodn::
   name_id ::= @identifier
   name_decl ::= name @name_id : [(@index * ... * @index) ->] @base_type

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
   abstract_function_decl ::= abstract @fun_id {? [@tvar_params]} : @type

Abstract function declarations can be :ref:`polymorphic<section-polymorphism>` through the optional
:n:`@tvar_params` type variable parameters.

An abstract function must be used in prefix notation if its name is an
:n:`@identifier`, and in infix notation if its name is an
:n:`@infix_op` (note the parenthesis around :n:`(@infix_op)` in the
declaration).

.. example:: 
             
   Equality is defined in Squirrel as the polymorphic abstract function 
   :g:`abstract (=) ['a] : 'a -> 'a -> bool`.
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

:gdef:`Operators <operator>` are function symbols with a concrete user-defined semantics.
An operator's semantics must be *deterministic*.

.. prodn::
   op_id ::= @identifier | (@infix_op)
   operator ::= op @op_id {? [@tvar_params] } @binders {? : @type } = @term

An operator declaration *fails* if Squirrel cannot syntactically check
that its body represents a deterministic value.

Operator declarations can be :ref:`polymorphic<section-polymorphism>` through the optional
:n:`@tvar_params` type variable parameters.

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


Macros
------

:gdef:`Macros <macro>` are a special built-in *probabilistic*
functions defined by recurence over the execution trace (i.e. the 
:g:`timestamp` type). A new set of macros is defined whenever a system
is declared, see the :ref:`system-defined macro section
<section-system-macros>`.

Macros can occur in terms, and their syntax is as follows:

.. prodn::
   macro_id ::= @identifier
   macro ::= @macro_id {* @term} @ @term

The timestamp argument :n:`ts` of a macro :n:`@macro_id` is passed using a special syntax :n:`@macro_id @ ts`.

The term :n:`@macro_id @term__1 ... @term_n @ @term__t` represents the
application of macro symbol :n:`@macro_id` which arguments
:n:`@term__1 ... @term_n` at a time-point :n:`@term__t` (of type
:g:`timestamp`).

.. todo::
   Adrien: incomplete, as *global* and *state* macros are not presented here.   

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
   channel_decl ::= channel @channel_id

   
.. _section-mutable-state:

Mutable state
-------------

Processes are allowed to manipulate states, defined with an
identifier, a replication indices, the type of term stored inside the
state and the initial value of the state:

.. prodn::
   state_id ::= @identifier
   state_decl ::= mutable @state_id @binders {? : @type} = @term

A memory cell can only be indexed by arguments of type :g:`index`.
   
.. example:: State counter
	     
   :g:`mutable counter (i,j,k:index) : message = zero` declares a set
   of counter states indexed by :g:`i,j,k`, all initialized to
   :g:`zero`.

.. todo::
   Adrien: I think this description is not accurrate.
   
Process declaration
-------------------

The basic process constructs are:

.. prodn::
   basic_process ::= new @name_id | @state[({*, @term})] := @term | out(@channel, @term) | in(@channel, @term)

A basic process can be:

 * The binding of a name with :g:`new name`, which implicitly declares
   a new :term:`name symbol<name>` indexed by the current replication indices. This
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
    process_decl ::= process @process_id @binders = @proc	

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
   system_id ::= @identifier
   system_decl ::= system {? [@system_id]} @process

As processes are defined over bi-terms, we in fact declare here a :gdef:`bi-system`, refering to the left and right protocols made up when projecting on the left or the righ the bi-terms. If no system identifier is specified, the :n:`default` name is used.

.. example:: System declarations

	     Using the previously defined :n:`Dummy` process, we
	     define a system with :g:`system [myProtocol] Dummy`.
	     Another distinct system could be declared with :g:`system
	     (Dummy | out(c,empty))`, which would this time be named
	     :n:`default`.

System expressions and contexts
+++++++++++++++++++++++++++++++

Systems can be refereed to, notably in proof goals and axioms, using system expressions:

.. prodn::
   single_expr ::= @system_id/left | @system_id/right
   pair_expr ::= @system_id | @single_expr, @single_expr
   system_expr ::= any | @pair_expr
   system_context ::= set: @system_expr; equiv:  @pair_expr | @system_id

.. todo::
   Adrien: describe single system as well as pairs and sets of systems.
   
A *concrete system context* :g:`set:S; equiv:P` comprises:
* a set of systems :g:`S` used to interpret :term:`reachability atoms<reachability atom>`
* a pair of systems :g:`P` used to interpret :term:`equivalence atoms<equivalence atom>`.

A *system context alias* :g:`S` --- where :g:`S` is a :n:`@system_id`,
hence a bi-system --- is syntactic sugar for :g:`set:S; equiv:S/left,S\right`.

.. _section-system-macros:

System-defined macros
+++++++++++++++++++++


Whenever a system is declared, for each action `A[idx]` inside the system with output value `o(x)` and condition `c(x)` where `x` denotes the input of action `A[idx]`, multiple mutually recursive macros are declared:

* :g:`output@A[idx] := o(input@A[idx])`.
* :g:`cond@A[idx] := c(input@A[idx])`.
* :g:`input@A[idx] := att(frame@pred([idx]))`.
* :g:`frame@tau` is equal to :g:`<frame@pred(tau), if cond@tau then output@tau>` if :g:`tau` happens and is not the first timestamp :g:`init`. Otherwise, :g:`frame@tau` is :g:`empty`.
* :g:`exec@tau` is equal to :g:`exec@pred(tau) && cond@tau>` if :g:`tau` happens and is not the first timestamp :g:`init`. Otherwise, :g:`exec@init` is :g:`true`.


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
defaults to system :n:`[default]`) named :n:`@goal_id`.  This
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
