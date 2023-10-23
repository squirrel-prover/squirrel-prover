.. _section-declarations:

============
Declarations
============

Declarations allow to introduce the various kinds of objects
that are used to model protocols and security properties in Squirrel.
Declared objects may be purely abstract, carry assumptions,
or have a concrete, explicit meaning.

Terms
=====
        
Names
-----

Names are used to model random samplings.

.. prodn::
   name_id ::= @ident

.. decl:: name @name_id : {? @type ->} @type

  A name declaration :n:`name @name_id : {? @type__i ->} @type__s` introduces
  a new name symbol :n:`@name_id` optionally indexed by :n:`@type__i` and
  sampling values of type :n:`@type__s`.

  Whenever a name :g:`n` is defined, a corresponding
  :gdef:`namelength axiom` is declared as:
  
  .. squirreldoc::
     axiom [any] namelength_n : [len (n) = namelength_message]

  It states that all names have the same length, given by a constant.
  
  It is required that the indexing type :n:`@type__i` is a
  :term:`finite` type, but there are no restrictions over the sampling type
  :n:`@type__s`. 
   
  The sampling *distribution* used over the sampling type :n:`@type__s`
  is usually arbitrary --- though it can be restricted using 
  :term:`type tags<type tag>`.

Two distinct applied name symbols, or the same name symbol applied to
two different index values, denote **independent** random samplings
(using the same distribution).
This is reflected by the :tacn:`fresh` tactic.


Abstract functions
------------------

:gdef:`Abstract functions<abstract_fun>` model
arbitrary functions over which no assumptions are made,
apart from the fact that
they are *deterministic* and *polynomial-time computable*.
In other words, their implementation cannot depend on the random
tapes, but it may still depend on the security parameter :math:`\eta`.
If needed, their behaviour can be restricted further through
:term:`axioms<axiom>`.

.. prodn::
   fun_id ::= @ident | (@infix_op)

.. decl:: abstract @fun_id {? [@tvar_params]} : @type

  Declares a deterministic and polynomial-time computable abstract
  function of type :n:`@type` and named :n:`@fun_id`.

  The function can be :ref:`polymorphic<section-polymorphism>` 
  through the optional :n:`@tvar_params` type variable parameters.

An abstract function must be used in prefix notation if its name is an
:n:`@ident`, and in infix notation if its name is an
:n:`@infix_op` (note the parentheses around :n:`(@infix_op)` in the
declaration).

.. example:: 
             
   Equality is defined in Squirrel as an axiomatized polymorphic
   abstract function:

   .. squirreldoc::
      abstract (=) ['a] : 'a -> 'a -> bool

Operators
---------

Operators are function symbols with a concrete user-defined semantics.
An operator's semantics must be *deterministic*.

.. prodn::
   operator_id ::= @ident | (@infix_op)

.. decl:: op @operator_id {? [@tvar_params] } @binders {? : @type } = @term

   Declares an operator named :n:`@op_id`, with arguments :n:`@binders` and
   returning :n:`@term`.

   The return type :n:`@type` can be provided, or left to be
   automatically inferred by Squirrel.
  
   Operator declarations can be :ref:`polymorphic<section-polymorphism>` through 
   the optional :n:`@tvar_params` type variable parameters.

   An operator declaration *fails* if Squirrel cannot syntactically check
   that its body represents a deterministic value.

An operator must be used in prefix notation if its name is an
:n:`@ident`, and in infix notation if its name is an
:n:`@infix_op` (note the parentheses around :n:`(@infix_op)` in the
declaration).

..
  As recursion is not yet supported, this is in fact currently syntact
  sugar for declaring an :term:`abstract function <abstract_fun>` symbol along with an :term:`axiom` stating
  the equation giving its defintion.


Built-ins
+++++++++

Squirrel features several :gdef:`built-in` function symbols
with built-in axiomatizations.

* :n:`if @term then @term else @term`,
  used in :term:`terms <term>`, may theoretically be viewed
  as a built-in.
* :n:`happens(@term)`, :n:`pred(@term)` and :n:`init` are three
  function symbols dealing with the :term:`timestamp` type. Each model
  instantiates the set of timestamps by specifying which ones actually happen
  on the given trace, and for all the ones that happen, their total
  ordering, :n:`init` refering to a fixed first timestamp and
  :n:`pred` being the predecessor function.
* The boolean connectors of :term:`local formulas<local formula>` are built-ins:
  :n:`true`, :n:`false`, :n:`&&`, :n:`||`, :n:`=>`, :n:`<=>` and :n:`not`.
* Comparison functions :n:`=`, :n:`<>`, :n:`<=`, :n:`<`, :n:`>=` and :n:`>`.
* A witness function :n:`witness`.
* A dedicated :n:`xor` symbol along with its :n:`zero`.
* A conversion function from :g:`bool` to :g:`message`, :n:`of_bool`.
* Utility constants for failure, :n:`fail`, and an empty message, :n:`empty`.
* The successor function over natural numbers `succ`.
* The pairing function :n:`pair` (also noted :n:`<x,y>`) with
  its projection functions :n:`fst` and :n:`snd`.
* A length function for the number of bits in a message, :n:`len`, as well as a function producing a bitstring of zeroes of the same length as its input, :n:`zeroes`.
   

Cryptographic functions
-----------------------

Squirrel allows to declare functions modelling standard
:gdef:`cryptographic functions <cryptographic function>` with
associated cryptographic assumptions.

.. prodn::
   crypto_ty_arg ::= @ident : @type
   
Types over which the cryptographic functions operate can be specified
using :n:`@crypto_ty_arg`, where :n:`@ident:@type` states that the argument
named :n:`@ident` is of type :n:`@type`. See the declarations below for 
a description of which argument names can be provided for each tactic.
If no argument is provided for :n:`@ident`, :n:`@type` default to :g:`message`.

.. decl:: hash @fun_id {? where {+ @crypto_ty_arg}}

   .. squirreldoc::
      hash h where m:tym h:tyh k:tyk

   declares a keyed :gdef:`hash function <hash function>` with types
   :g:`tyk` for keys, :g:`tym` for messages and :g:`tyh` for hash
   digests.
   It is assumed to satisfy the PRF and known-key collision
   resistance assumptions.

   Enables the use of :tacn:`prf`, :tacn:`euf` and :tacn:`collision`.   
         
.. decl:: signature @fun_id, @fun_id, @fun_id {? where {+ @crypto_ty_arg}}

   .. squirreldoc::
      signature sig, ver, pk where m:tym sig:tysig sk:tysk pk:typk
      
   declares a :gdef:`signature scheme` with types :g:`tym` for
   messages to be signed, :g:`tysig` for signatures, :g:`tysk` for
   secret signing keys and :g:`typk` for public verification keys.
   It is assumed unforgeable against
   chosen message attacks (EUF-CMA) and satisfying the equation
   :g:`ver(sig(m,sk),m,pk(sk)) = true`.

   Enables the use of :tacn:`euf`.

.. decl:: aenc @fun_id, @fun_id, @fun_id {? where {+ @crypto_ty_arg}}

   .. squirreldoc::
      aenc enc, dec, pk where ptxt:typtxt ctxt:tyctxt rnd:tyrnd sk:tysk pk:typk
     
   declares an :gdef:`asymmetric encryption` scheme with types
   :g:`typtxt` for plain-texts, :g:`tyctxt` for cipher-texts,
   :g:`tyrnd` for encryption randomness, :g:`tysk` for secret decryption keys and
   :g:`typk` for public encryption keys.
   It is assumed IND-CCA1 and ENC-KP, and satisfying the equation
   :g:`dec(enc(m,pk(sk)),sk) = m`.
      
   Enables the use of :tacn:`cca1` and :tacn:`enckp`.
   

.. decl:: senc @fun_id, @fun_id, @fun_id {? where {+ @crypto_ty_arg}}

   .. squirreldoc::
      senc enc, dec where ptxt:typtxt ctxt:tyctxt rnd:tyrnd k:tyk

   declares a :gdef:`symmetric encryption` scheme with types
   :g:`typtxt` for plain-texts, :g:`tyctxt` for cipher-texts,
   :g:`tyrnd` for encryption randomness and :g:`tyk` for keys.
   It is assumed IND-CPA and INT-CTXT, and satisfying the equation
   :g:`dec(enc(m,sk),sk) = m`.
      
   Enables the use of :tacn:`cca1`, :tacn:`intctxt` and :tacn:`enckp`.

.. decl:: {| ddh | cdh | gdh } @fun_id, @fun_id {? ,@fun_id} {? where {+ @crypto_ty_arg}}

   The :gdef:`group declaration`:
   
   .. squirreldoc::
      ddh g, (^), ( ** ) where group:tyg exponents:tye

   declares a group with generator :g:`g`, exponentation :g:`(^)` and
   exponent multiplication :g:`( ** )`.  The group is assumed to
   satisfy the DDH assumption when declared with :g:`ddh`, the CDH
   assumption with :g:`cdh`, and the Gap-DH assumption with g:`gdh`.
   
   Enables the use of :tacn:`cdh`, :tacn:`gdh` and :tacn:`ddh`.

.. _section-processes:

Processes
=========

Protocols are modelled as systems, which provide a meaning to macros
(e.g., :g:`output`, :g:`cond`) used in our logic. Systems are themselves
defined through processes written in a dialect of the applied pi-calculus.

.. note::
  The first presentations of Squirrel's logic relied explicitly on
  notions of systems, first without state :cite:`bdjkm21sp` and then
  with state :cite:`bdkm22csf`. The latest presentation
  :cite:`bkl23hal` does not feature a notion of system, but
  allows to encode systems through a more expressive logic.
  So far, the translation from processes to systems has not been
  formally defined in the literature.

.. _section-channel:

Channels
--------

Communications over the network are performed over public channels, identified by a name.

.. prodn::
   channel_id ::= @ident

.. decl:: channel @channel_id

   Declares a channel named :n:`@channel_id`.
 
  
.. _section-mutable-state:

Memory cells
------------

Processes in Squirrel can use mutable states.

.. prodn::
   state_id ::= @ident

.. decl:: mutable @state_id @binders {? : @type} = @term
  
   Declares a memory cell named :n:`state_id` indexed by arguments
   :n:`@binders` and initialized to :n:`term`.
   Due to technical limitations, Squirrel currently only supports
   :n:`@binders` of :term:`finite` type.

   The return type :n:`@type` can be provided, or left to be
   automatically inferred by Squirrel.
   
.. example:: State counter
       
   A set of mutable counters indexed by :g:`i,j,k`, all initialized 
   to :g:`zero`, may be declared as follows:

   .. squirreldoc:: 
      mutable counter (i,j,k:index) : message = zero

   With this declaration, the following formula is valid:

   .. squirreldoc::
      forall i j k, counter (i,j,k) @ init = zero
   
Processes
---------

We first introduce process prefixes, which correspond to basic operations
performed by processes:

.. prodn::
   process_prefix ::= new @name_id 
   | @state_id {? ({*, @term})} := @term
   | out(@channel, @term) 
   | in(@channel, @term)

The last three prefixes correspond to the update of a
:ref:`memory cell<section-mutable-state>`, and input and
asynchronous output over a :ref:`channel<section-channel>`.
Their semantics is straightforward.

From a process semantics viewpoint, :g:`new name` samples a new
random value. From a logical viewpoint, this is reflected by
declaring a new name, indexed by the current replication indices. This
is syntactic sugar that can be avoided by manually declaring the
needed name symbols with the appropriate arities before the process
declaration.

Processes are then built from prefixes using parallel composition,
(indexed) replication and conditionals, as well as other common
constructs:

..  prodn::
    process_id ::= @ident
    alias ::= @ident
    process ::= null
    | @process_prefix
    | @process_prefix; @process
    | @process | @process
    | if @term then @process {? else @process}
    | try find @binders such that @term in @process {? else @process}
    | let @ident = @term in @process
    | !_@ident @process
    | @process_id {? ({*, @term}) }
    | @alias : @process

The construct :g:`A : proc` does not have any semantic impact: it is
only used to give an alias to this location in the process.

.. decl:: process @process_id @binders = @proc
   
   Declares a new process named :n:`@process_id` with arguments :n:`@binders`
   and body :n:`@process`.


Systems and actions
-------------------

Squirrel's logic only deals with systems, which are obtained
by translating protocols. Systems are (partially ordered) sets of actions,
which correspond to atomic execution steps of a protocol comprising:

* the reception of a message input from the (malicious) network;
* the verification of an executability condition;
* and, if the action is executable, the output of a message to the network.

A system can currently only be defined from a process.
For the same reasons that make :term:`multi-terms<multi-term>` useful,
it is useful to define multiple systems at once (i.e., a multi-system)
using a process featuring multi-terms.

.. prodn::
   system_id ::= @ident

.. decl:: system {? [@system_id]} @process

   Declare a :gdef:`bi-system` whose actions are obtained by
   translating :n:`@process`, which may use bi-terms.
   The obtained :gdef:`single systems<single system>` can be referred to as
   :g:`system_id/left` and :g:`system_id/right`.
   The left (resp. right) single system corresponds to the process
   obtained by taking the left (resp. right) projections of all bi-terms
   appearing in :n:`@process`.

   The system name :n:`@system_id` defaults to :n:`default` when no
   identifier is specified.

Actions are referred to through identifiers:

.. prodn::
   action_id ::= @ident

When translating processes into sets of actions, fresh action
identifiers are automatically generated to name created
actions. Alternatively, the user can give a naming hint using the
:n:`@alias` process construct. Note however that Squirrel may not
respect such naming hints.

Internally, an action is defined by:

* an :gdef:`action identifier or constructor<action constructor>` :n:`@action_id`;
* a list of :g:`index` variables corresponding to surrounding replications
  and :g:`try find` constructs;
* a :n:`@term` of type :g:`bool` representing the action executability condition;
* a term of type :g:`message` representing the action output.


.. example:: Actions corresponding to a process definition
       
   Consider the following system declaration:

   .. squirreldoc::
      abstract one : message.
      name n : index -> message.
      channel c.

      system
        (!_i (in(c,x);
              if x=zero then
                A: out(c,n(i))
              else
                B: out(c,x)
        ) | in(c,x); out(c,empty)).
  
   The provided process yields a system with three actions:
   
   * action :n:`A[i]`, which on input :g:`x` checks whether :g:`x=zero` and outputs :g:`n(i)`;
   * action :n:`B[i]`,  which on input :g:`x` checks whether :g:`x<>zero` and outputs :g:`x`;
   * and action :n:`A1` (automatically named) which checks whether :g:`true` and outputs :g:`empty`.  

.. _section-system-macros:

System-defined macros
+++++++++++++++++++++

Declaring a system provides a meaning to several macros for the
system's actions. Given an action :g:`A(indices)`
with output value :g:`o(x)` and condition :g:`c(x)` over the input :g:`x`,
the following holds:

* :g:`output@A(indices) = o(input@A(indices))`;
* :g:`cond@A(indices) = c(input@A(indices))`;
* :g:`input@A[indices] = att(frame@pred(A(indices)))`.

Other macros have a meaning that does not depend on the specific
action:

* :g:`frame@tau = <frame@(pred tau), exec@tau, if exec@tau then output@tau>` 
  provided that :g:`tau` happens and is not the initial timestamp
  :g:`init` (otherwise, :g:`frame@tau` is :g:`empty`);
* :g:`exec@tau = exec@(pred tau) && cond@tau>` provided that
  :g:`tau` happens and is not the initial timestamp
  :g:`init` (otherwise, :g:`exec@init` is :g:`true`).

System expressions
++++++++++++++++++

:gdef:`System expressions<system expression>` describe one or several systems.
We first introduce single system expressions:

.. prodn::
   single_system_expr ::= @system_id/left | @system_id/right

Here, :n:`@system_id/proj` is an unlabelled single system 
representing the left (if :n:`proj = left`) or right (if :n:`proj = right`)
component of the :term:`bi-system` named :n:`@system_id`.


.. prodn::
   system_expr ::= any | @system_id | {*, @single_system_expr}

A system expression may be generic (:g:`any`, corresponding to any system,
already declared or not) or specify a fixed list of systems, each
of them coming with a label identifying it.
When :n:`@system_id` is a :gdef:`multi-system`,
the system expression :n:`@system_id` corresponds to the list of
its single systems, with the labels that they carry in this multi-system.
A system expression can also be explicitly formed as
:n:`@single_system_expr__1,...,@single_system_expr__n`.
In this case, the labels are:

  + ε if :n:`n = 1`;

  + :n:`left` and :n:`right` if :n:`n = 2`;

  + the :n:`n` first positive integers otherwise.

System contexts
+++++++++++++++
  
.. prodn::
   system_context ::= set: @system_expr; equiv:  @system_expr
   | @system_id

A *concrete system context* :g:`set:S; equiv:P` comprises:

* a multi-system specified by :g:`S` used to interpret
  :term:`reachability atoms<reachability atom>`;

* a pair of systems (i.e. a multi-system with two elements) :g:`P`
  used to interpret :term:`equivalence atoms<equivalence atom>`.

A :n:`@system_id` :g:`S` can also be used as a system context:
it stands for :g:`set:S; equiv:S/left,S/right`.

   
Axioms and Lemmas
=================

Squirrel supports two kinds of :gdef:`lemmas<lemma>`, one for each kind of formulas:
:gdef:`local lemmas<local lemma>` for :term:`local formulas<local formula>` and
:gdef:`global lemmas<global lemma>` for :term:`global formulas<global formula>`.
Similarly, there are local and global
:gdef:`axioms<axiom>`. The only difference between a lemma and an axiom
declaration is that the former creates a proof-obligation that must be
discharged by the user through a :ref:`proof<section-proofs>`.

.. prodn::
   statement_id ::= @ident 
   local_statement ::= {? [@system_expr] } {| @statement_id | _} {? [@tvar_params]} @binders : @formula
   global_statement ::= {? [@system_context] } {| @statement_id | _} {? [@tvar_params]} @binders : @global_formula

A local statement as described above expresses that
the local formula :n:`forall @binders, @formula` holds
in the context :n:`[@system_expr]` (which
defaults to :n:`[default]`).
The statement is named :n:`@statement_id` for future reference.

Similarly,
a global statement expresses that
:n:`Forall @binders, @global_formula` holds in the context
:n:`[@system_context]` (which defaults to :n:`[default]`).

Local and global statements can be
:ref:`polymorphic<section-polymorphism>` through the optional
:n:`@tvar_params` type variable parameters (they hold for all
instances of the given type variables).

Unnamed (local and global) statements can be declared using an
underscore :g:`_` instead of a statement identifier
:n:`@statement_id`.
                      
.. decl:: {? local} {| lemma | axiom } @local_statement
   :name: lemma
   
   Declares a new local :g:`lemma` or :g:`axiom`.

.. decl:: global {| lemma | axiom} @global_statement
   :name: global

   Declares a new global :g:`lemma` or :g:`axiom`.

.. example:: Local axioms and lemmas
       
   We declare an axiom stating
   that in any system, a pair has a negligible probability of
   being equal to the constant :g:`fail`.

   .. squirreldoc::
      axiom [any] fail_not_pair (x,y:message): <x,y> <> fail

   Next, we state that in system :g:`[default]`,
   the adversary never sends the same message twice.

   .. squirreldoc::
      axiom no_repeat t t' : happens(t,t') => t <> t' => input@t <> input@t'

   Finally, the following unnammed local lemma states that, for the
   single system :g:`myProtocol/left`,
   action :g:`A2` can execute only if the adversary sends the message
   :g:`ok` at time-point `A1`:

   .. squirreldoc::
      lemma [myProtocol/left] _ : cond@A2 => input@A1 = ok

.. example:: Global lemmas

  The next (typical) global lemma states that the two projections
  of the bi-system :g:`myProtocol` are observationally equivalent:

  .. squirreldoc::
     global lemma [myProtocol] obs_equiv (t:timestamp[const]) : [happens(t)] -> equiv(frame@t)

  As a slight variant,
  we now state that :g:`real/left` and :g:`ideal/right`
  are observationally equivalent, this time using only :g:`real/left`
  to interpret :g:`[_]` atoms (which does not change anything in that
  case since :g:`happens(_)` does not depend on the details of system
  actions):

  .. squirreldoc::
     global lemma [set: real/left; equiv: real/left,ideal/right] ideal_real_equiv :
       Forall (tau:timestamp[const]), [happens(tau)] -> equiv(frame@tau)
