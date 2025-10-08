.. _section-typing:

==================
Typing for secrecy
==================

This section describes the typing tactic enabled by
:g:`set securityTypes = true`.
The user must give types when declaring names and mutable states
describing which messages are public or secret.
Then, Squirrel will type-check all systems in the file
when they are defined.
Finally, the :tacn:`typing` tactic proves that a public term,
i.e., a message possibly known by the attacker,
cannot be equal to a secret term.

.. note::
  This tactic implements the work published in :cite:`bdjkm21sp`.

.. flag:: securityTypes

  Allows to declare security types and to use the :tacn:`typing` tactic.

Types
=====

Types used to express security guarantees are different from the usual
types defined by the :token:`@type` production. They do not replace them,
but are used in addition to them.

To typecheck a term, the user must have assigned a security type to some base
elements of that term (i.e. names and mutable states).
There are two kinds of security types: types for messages and types for keys.

.. prodn:: message_type ::= Msg
           | High
           | Low
           | Bool
           | Cst @fun_id
           | @message_type * @message_type
           | @message_type + @message_type

A message type describes the level of knowledge the attacker may have on a
term with that type.

* :n:`Msg` is the most general type: it does not give any guarantee.
* :n:`High` means the term is secret: its exact value cannot be
  computed from public values
  (except with negligible probility).
  However, some bits of information about it could be publicly available.
* :n:`Low` is the type of a value that may be published.
* :n:`Bool` is the type of a boolean value. These values are always public.
* :n:`Cst c` designates a term overwhelmingly interpreted
  as the constant :n:`c`.
  The identifier `c` must designate an abstract function
  with a type of the form :n:`{* index -> } message`.
* :n:`T_1 * T_2` designates a pair of a term of type :n:`T_1` and one of type :n:`T_2`.
* :n:`T_1 + T_2` is a sum type: a term of this type will be
  a term of type :n:`T_1` in some executions, and of type :n:`T_2` in others.

.. prodn:: key_type ::= SK[@fun_id, @message_type]
           | AK[@fun_id, @message_type]
           | SSK[@fun_id, @message_type]

A key type describes an honest uncompromised key for encryption/signature:

* :n:`SK[f, T]` is a symmetric encryption key.
  :n:`T` is the type of the plaintexts that can be encrypted with this key.
  :n:`f` must be the associated encryption function,
  declared using :decl:`senc`.
* :n:`AK[f, T]` is an asymmetric encryption private key.
  :n:`T` is the type of the plaintexts that can be encrypted with this key
  by honest agent in the protocol.
  :n:`f` must be the associated encryption function,
  declared using :decl:`aenc`.
* :n:`SSK[f, T]` is a signature private key.
  A signature with this key ensures the signed message is of type :n:`T`.
  :n:`f` must be the associated signature function,
  declared using :decl:`signature`.


.. prodn:: security_type ::= @message_type
           | @key_type
           | Rand

A security type is either a message type, a key type,
or :n:`Rand`, a special type reserved for randomness used when encrypting.
To encrypt a message typed :n:`T` with a key typed :n:`SK[f, T]`
or :n:`AK[f, T]`, the randomness given to the encryption function
must be typed :n:`Rand`.
The type system checks, among other conditions,
that the same random is not used twice.

Typing algorithm
================

The typing procedure does not support all features of Squirrel's language.
In particular, it cannot consider terms with user-defined types, higher-order,
or names and mutable states with non-index arguments.

The typing procedure is sound w.r.t the type system described in
:cite:`bdjkm21sp`, but it is not complete.
One notable source of incompleteness is a rule of the type system
that allows, when a variable is known to be of type :n:`T_1 + T_2`,
to perform a case disjunction, and continue the typechecking twice,
assuming first that the variable has type :n:`T_1`, and then :n:`T_2`.
One must be careful when applying that rule, since it may lead to the same
randomness being apparently used in different encryptions, once in each
branch of the proof.
Typing may thus require a subtle use of that rule to break sums.
The implemented algorithm relies on a heuristic to decide when to apply it,
which is not complete.
As much as possible, when typechecking fails because of the heuristic, the
error message reports it.


Declarations
============

The flag :flag:`securityTypes` modifies the syntax and/or behaviour of some
declarations.
Once it is set to :n:`true`, the user can add security types
to name and mutable state declarations.

Name declarations
-----------------

.. declv:: name @name_id : {? @type -> } @type {? , @security_type }
          
  A name declaration :n:`name @name_id : {? @type__i ->} @type__s` introduces
  a name symbol :token:`name_id`, with a user-defined :token:`security_type`.
  The same constraints on :n:`@type__i` and :n:`@type__s` as on normal
  name declarations apply.
  A name can only be declared with types :n:`Low`, :n:`High`, :n:`Rand`,
  or a :token:`@key type`.
  Additionally, a security type other than :n:`Low` can only be declared
  if the type in which the name is sampled is tagged :n:`large`.


State declarations
------------------

.. declv:: mutable @state_id @binders {? : {| @type | @security_type | @type, @security_type } } = @term
  
  Declares a mutable state with a user-defined @security_type.
  The same restrictions on :n:`@binders` and :n:`@type` as usual apply.

  When using a :n:`@security_type`, :n:`@type` must be :n:`message`.

  If the :n:`@term` provided as initial value cannot be typed with the given
  :n:`@security_type`, then the mutable state :n:`@state_id` is not well-typed.
  Since, when declaring a state, action :n:`init` is updated in all systems
  to set its initial value, any past or future system immediately stops being well-typed
  as well, and a warning is displayed to the user.

  
Protocol declarations
---------------------

The syntax for protocol declarations is unchanged.
However, each system is typechecked when it is declared.
The typechecker ensures all outputs are :n:`Low`,
all conditions are :n:`Bool`, and each update of a mutable state
sets it to a value of the expected type, provided at the state's declaration.
These verifications are performed separately on each projection of the system, unless the
system does not use the :n:`diff` operator, in which case it is only typechecked once.

When declaring a system, some proof obligations may be opened.
Indeed, to typecheck some terms, the type system may need to assume that
some constants with different symbols are different -- typically, constants used as
tags to distinguish protocol messages.
If the typechecker makes this assumption, and cannot automatically prove it holds,
it opens a subgoal asking the user to prove it, before declaring the system to be well-typed.

The :tacn:`typing` tactic is enabled in all well-typed projections of a system, but
is unavailable in projections where the typechecking failed.
In that case, a message describing the action in which the error occurred is displayed.


Tactic
======

.. tacn:: typing @hypothesis_id

  This tactic applies to a hypothesis of the form :n:`t_1 = t_2`.
  The current goal's :n:`@system_context` must specify a set consisting
  in a finite number of well-typed (projections of) systems.
  The tactic attempts to give :n:`t_1` the type :n:`Low` and :n:`t_2` the type :n:`High`,
  or vice-versa if that first attempt fails, in each system of the set.
  These typing derivations cannot use encryption randomness, of type :n:`Rand`.

  The :tacn:`typing` tactic does not unfold macros, and it may thus be necessary
  to unfold global macros and conditions manually.

  Like for protocol declarations, typechecking can open subgoals:

  * Again, if typechecking :n:`t_1` and :n:`t_2` requires the assumption that some constants are different,
    a proof obligation is generated for it.
  * If a subterm of the form :g:`output@tau` appears in :n:`t_1` or :n:`t_2`, the user must prove
    that it appears under a condition that implies :g:`exec@tau`.
  * If a mutable state :g:`s@tau` appears in :n:`t_1` or :n:`t_2`, the user must prove
    that it appears under a condition that implies :n:`happens(tau)`.

  In these subgoals, not all hypotheses from the original proof context are sound to keep,
  according to the soundness proof of the type system in :cite:`bdjkm21sp`.
  The tactic only keeps global hypotheses, and local hypotheses that are either
  :n:`[const]` or of type :n:`Bool` in the type system.

  If typechecking succeeds, the hypothesis :n:`@hypothesis_id` is contradictory,
  and :tacn:`typing` closes the original goal.
  If typechecking fails in one or more systems, the tactic fails, and
  displays the errors obtained by both attempts at typing (:n:`t_1:Low`/:n:`t_2:High` and the converse).
