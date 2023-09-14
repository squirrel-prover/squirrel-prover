.. _tutorial:

.. Gentle introduction to Squirrel

This tutorial provides a very quick introduction to the main concepts
of Squirrel. It can be used to ease its discovery and to get an
intuitive grasp of the multiple concepts by going through a concrete
example. The reference manual provides a more extensive presentation
of all the concepts.

Protocol modelling
--------------------

Squirrel allows to perform proofs of security for communication
protocols. It works whitin a high-order logic, and a first step is to
be able to model all the components of a protocol inside a logic.

Messages
++++++++

Messages computed and exchanged by a protocol and sent over the
network are modelled using *terms*.

Concretely, a term is built from

 * a name :g:`n` used to model a random sampling;
 * applications of functions :g:`f(m_1,...,m_k)`.

Notice that this allow to effectively model any computation, as one
can have function symbols modeling any sort of computations, from
equality testing, to conditional branching, to encryption funcitions.

In **Squirrel**, a function symbol without any assumption can be defined with:


.. squirreltop::  in

   abstract ok : message
   abstract ko : message
   abstract f1 : message -> message
   abstract f2 : message * message -> message.


When using such function symbols inside a protocol, we are effectively
saying that those function symbol may be in practice instantiated by
any function of the correct type. This is notably usefull to model a
constant `ok`, without giving any specific concrete value to this
constant.

`ok` and `ko` are constants, and `f1` is a function that expects a message, and
then return a message. `f2` is then a function symbol of arity two, and function
symbols of any arity can be defined this way.


A name `n` allows to model secret keys, or some random challenge. As we wish to
be able to refer to an unbounded number of session, we allow names to be
indexed, each value of the index yielding a fresh independent random value. We denote
by `n[i]` an indexed name, with variable `i` as an index. Names can be indexed
by any number of indices.

In the tool, one can declare names and indexed names with the following.

.. squirreltop::  in

   name n : message
   name n1 : index -> message
   name n2 : index * index -> message.


Compare to game based cryptography, one can think about names as
picking at the begining of the protocol execution all possible random
values that will be needed, and store them within indexed cells, which
are our names.
   
To model a setting where multiple people each have their own secret key,
one could declare an indexed name as follows.


.. squirreltop::  in

   name key : index -> message.


Basic assumption   
++++++++++++++++


We can declare axioms over our abstract function symbols, for instance
to state that the two abstarct constant :g:`ok` and :g:`ko` are not
equal.



.. squirreltop::  in
		  
   axiom [any] ok_not_ko: ok <> ko.

Axioms are formulas in a high-order logic, for instance allowing free
variables, universal and existential quantification, implications,
etc. Here, we define the axiom as true over :g:`any` protocol.

Another axiom that could be useful to prove the security of a protocl
is for instance that :g:`ko` can never be equal to any pair
:g:`<x,y>`.

.. squirreltop::  in
		  
   axiom [any] ok_not_pair (x,y:message): <x,y> <> fail.


Going back to the name declaration, if we now display the Squirrel output after a declaration, we see the following:

.. squirreltop::  all

   name skey : index -> message.

This means that whenever a new name is declared, we also create a
dedicated axiom stating that the length of the name (which is a random
bitstring) is equal to some constant, which means that all names have
the same length.

Cryptographic assumptions
+++++++++++++++++++++++++

Symbol functions can be defined as being an encryption, or a hash function, or a
signature, or... The tool will then assume that such functions satisfy some
classical cryptographic assumptions.

The possible sorts and corresponding assumptions are:

 * encryption,  **CCA1** & **INT-CTXT**, symmetric and asymmetric
 * signatures, **EUF-CMA**
 * hash functions, **PRF**, and thus **EUF-CMA**, **CR**

Each are declared in the following way.

.. squirreltop::  in

   signature sign,checksign,pk
   hash h
   senc enc,dec
   aenc asenc,asdec,aspk.

Protocols
+++++++++

Protocols are described inside a pi-calculus. It is based on the following constructs:

 *  :g:`new n` id used to declare a fresh name; (this is optional, and equivalent to declaring the names as seen begore)
 * :g:`out(c,m)` is used to send the term `m` over the channel `c`;
 * :g:`in(c,x)` is used to receive some value from channel `c`, bound to the variable `x`;
 * :g:`act; P` correspond to the sequential composition of action `act` with process `P`;
 * :g:`process name(vars) = ...` allors to declare a process with a name, in which case using `name(vars)` inside another process unfold the process definition;
 * :g:`P | Q` is a parallel composition of two processes;
 * :g:`if phi then P else Q` is a conditional branching;  
 * :g:`try find vars such that phi in P else Q` is a global lookup over indices, it can be seen as a lookup inside a database.   
   

As an example, we use a small *RFID* based protocol, with a tag and a reader,
called the basic hash protocol :cite:`bruso2010formal`.



.. example:: Basic Hash
	     
   T --> R : <nT, h(nT,kT)>
   R --> T : ok


We first declare the channels used by the protocol. Remark that channels are
mostly byproducts of the theory, and do not play a big role.

.. squirreltop::  all

   channel cT
   channel cR.


We then define a first process of a protocol, which may correspond to
multiple identies, and thus depend on some index variable `i`.

.. squirreltop::  all

   process tag(i:index) =
     new nT;
     T : out(cT, <nT, h(nT,key(i))>).


We can then declare the reader.

.. squirreltop::  all

   process reader(j:index) =
     in(cT,x);
     try find i such that snd(x) = h(fst(x),key(i)) in
       R : out(cR,ok)
     else
      out(cR,ko).

And we finally declare the final system. We instantiate multiple copies
of the reader, and for each value `i`, we also instantiate multilpe copies of
:g:`tag(i)` with the replicaiton over `k`.

.. squirreltop::  all

   system ((!_j reader(j)) | (!_i !_k tag(i))).


A system declared this way is given the name `default`. Other systems can
be defined and given an epxlicit name. For instance, the following declare the
system `simple`, where each tag can only be executed once for each identity.

.. squirreltop::  all

   system [simple] ((!_j reader(j)) | (!_i tag(i))).


Reachability properties
-------------------------

We express reachabilities formulas inside a first-order logic. In this logic, terms can be of type :g:`message`, :g:`boolean`, :g:`index` and :g:`timestamp`.
The logic proves that formulas are true for all possible traces of the protocol, and for all possible values of the variable given this trace/

For instance, a timestamp variable `t` allows to talk about a given point inside a trace. `t` will intuitively have to take the value of some concrete action, e.g., `T(i)` or `R(j)` in our example.

Macros
++++++

To discuss about the value of the output performed at some timestamp, we use macros:

 * :g:`input@t` is the value given as input by the attacker to the action at t;
 * :g:`output@t` is the output performed by action at t;
 * :g:`cond@t` is the executability condition at t;
 * :g:`frame@t` is the sequence of all previous outputs up to t;
 * :g:`exec@t` is the conjonction of all executability conditions up to t.

Formulas
++++++++

It is then possible to write formulas that capture properties satisfied by all
executions of the protocol. For instance, the following formula describes that
the executability execution of the reader in fact implies some authentication
property, in the sense that there must exists an action T(i,k) that was executed
before the reader, and such the input of the reader corresonds to the name of
T(i,k).

.. squirreltop::  all

   goal wa :
     forall (i:index, j:index),
     happens(R(j,i)) =>
        cond@R(j,i) =>
            exists (k:index),
                 T(i,k) <= R(j,i) && fst(input@R(j,i)) = nT(i,k).


We write bellow the simple proof of this statement. Once inside a proof context, delimited by `Proof.` and `Qed.`, it is possible to get the list of available tactics by typing `help.`, and details about any tactic with `help tacticname.`

.. squirreltop::  all

   Proof.
     help.
     help intro.
     intro i j Hh Hc.
     expand cond.
     euf Hc.
     intro [k _].
     by exists k.
   Qed.



