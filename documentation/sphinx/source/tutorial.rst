.. _tutorial:

.. Gentle introduction to Squirrel

This tutorial provides a very quick introduction to the main concepts
of **Squirrel**. It can be used to ease its discovery and to get an
intuitive grasp of the multiple concepts by going through a concrete
example. The reference manual provides a more extensive presentation
of all the concepts.

In many cases, the concepts introduced here are also direct clickable
references to the more extensive presentation in the reference manual.

Protocol modelling
--------------------

Squirrel allows performing proofs of security for communication
protocols relying on cryptography. It works within a high-order logic,
and a first step is to be able to model all the components of a
protocol inside the logic.

Messages
++++++++

Messages computed by a protocol and sent over the
network are modelled using :ref:`terms <term>`.

Concretely, a term is built from

 * names :g:`n` used to model random sampling;
 * application of functions :g:`f(m_1,...,m_k)`.

This allows effectively modelling any computation, as one
can have function symbols modelling any sort of computations, from
equality testing to conditional branching or encryption functions.

In **Squirrel**, a function symbol without any assumption can be defined with:


.. squirreltop::  in

   abstract ok : message
   abstract ko : message
   abstract f1 : message -> message
   abstract f2 : message * message -> message.


When using such function symbols inside a protocol, we are effectively
saying that those function symbol may be in practice instantiated by
any function of the correct type. And a proof in such a model holds
for any possible implementation of those functions. This is notably
useful to model a constant `ok`, without giving any specific concrete
value to this constant.

`ok` and `ko` are constants, and `f1` is a function that expects a message, and
returns a message. `f2` is then a function symbol of arity two. Function
symbols of any arity can be defined similarly.


A name `n` typically allows to model secret keys or nonces. As we wish to
be able to refer to an unbounded number of sessions, we allow names to be
indexed, each value of the index yielding a fresh independent random value. An indexed
name is denoted by `n[i]`, with variable `i` as an index. Names can be indexed
by any number of indices.

In the tool, one can declare names and indexed names as follows.

.. squirreltop::  in

   name n : message
   name n1 : index -> message
   name n2 : index * index -> message.


Compared to usual game based cryptography, one can think about names as
sampling at the beginning of the protocol execution all possible random
values that will ever be needed, and store them within indexed cells, which
are our names.
   
To model a setting where multiple people each have their own secret key,
one could declare an indexed name as follows.


.. squirreltop::  in

   name key : index -> message.


Basic assumption   
++++++++++++++++


We can declare axioms over our abstract function symbols, for instance
to state that the two abstract constant :g:`ok` and :g:`ko` are not
equal.



.. squirreltop::  in
		  
   axiom [any] ok_not_ko: ok <> ko.

A proof made in such a model would then apply to any concrete
implementation in which :g:`ok` and :g:`ko` are given two distinct
concrete values.
   
Axioms are formulas in a high-order logic, for instance allowing free
variables, universal and existential quantification, implications,
etc. Here, we define the axiom as true over :g:`any` protocol.

Another axiom that could be useful to prove the security of a protocol
is for instance that :g:`ko` can never be equal to any pair
:g:`<x,y>`.

.. squirreltop::  in
		  
   axiom [any] ok_not_pair (x,y:message): <x,y> <> ko.


Going back to the name declaration, if we now display the **Squirrel**
output after a declaration, we see the following:

.. squirreltop::  all

   name skey : index -> message.

This means that whenever a new name is declared, we also create a
dedicated axiom stating that the length of the name (which is a random
bitstring) is equal to some constant. In other words, all names have
the same length.

Cryptographic assumptions
+++++++++++++++++++++++++

Function symbols can be defined as being encryption functions, hash functions,
signature functions, etc. The tool will then assume that such functions satisfy some
classical cryptographic assumptions.

Some possible primitives, and the corresponding assumptions, are:

 * symmetric and asymmetric encryption,
   **CCA1** & **INT-CTXT** (only in the symmetric case)
 * signature, **EUF-CMA**
 * hash function, **PRF**, and thus **EUF-CMA**, **CR**

Each is declared in the following way.

.. squirreltop::  in

   signature sign,checksign,pk
   hash h
   senc enc,dec
   aenc asenc,asdec,aspk.

Protocols
+++++++++

Protocols are described in a variant of the pi-calculus as
:ref:`processes <section-processes>`. They are defined by the following constructs:

 * :g:`new n` is used to declare a fresh name (this is optional, and equivalent to the style of name declarations described earlier);
 * :g:`out(c,m)` is used to send term `m` over channel `c`;
 * :g:`in(c,x)` is used to receive some value from channel `c`, bound to the variable `x`;
 * :g:`act; P` correspond to the sequential composition of action `act` with process `P`;
 * :g:`process name(vars) = ...` allows to give a name to a process: using `name(vars)` inside another process then unfold the process definition;
 * :g:`P | Q` is the parallel composition of two processes;
 * :g:`if phi then P else Q` is conditional branching;  
 * :g:`try find vars such that phi in P else Q` is a global lookup over indices, it can be seen as a lookup in a database.   

 

As an example, we use a small *RFID*-based protocol, with a tag and a reader,
called the basic hash protocol :cite:`bruso2010formal`.



.. example:: Basic Hash
	     
   T --> R : <nT, h(nT,kT)>
   
   R --> T : ok

Here, a tag :g:`T` sends to the reader :g:`R` a fresh challenge
:g:`nT`, authenticated via a MAC using the tag's key
:g:`kT`. Each tag has a distinct :g:`kT`, and the reader has a
database containing all of them.
   

We first declare the channels used by the protocol. Remark that channels are
mostly byproducts of the theory, and do not play a big role.

.. squirreltop::  in

   channel cT
   channel cR.


We then define the first process for the tags, which may correspond to
multiple identities, and thus depends on some index variable `i`.

.. squirreltop::  in

   process tag(i:index) =
     new nT;
     T : out(cT, <nT, h(nT,kT(i))>).


We now declare the process for the reader.

.. squirreltop::  in

   process reader =
     in(cT,x);
     try find i such that snd(x) = h(fst(x),kT(i)) in
       R : out(cR,ok)
     else
      R1 : out(cR,ko).

Finally, we declare the complete system. We instantiate multiple copies
of the reader process, and for each value `i`, we also instantiate multiple copies of
:g:`tag(i)` with the replication over `k`.

.. squirreltop::  all

   system ((!_j reader) | (!_i !_k tag(i))).


We see that with this declaration, in the resulting system after
processing, all outputs have been given a name, and each output
corresponds to a possible action that can be triggered by the
attacker. Here, the possible actions are :g:`(init,R,R1,T)`. 
Many axioms are created, expressing the fact that for instance
actions :g:`R1` and :g:`R` are mutually exclusive, as they
are exclusive branches; this is the
:g:`mutex_default_R1_R` axiom, stating that for any possible
execution, the two actions cannot both happen in the trace.
   
A system declared this way is given the name `default`. Other systems can
be defined and given an explicit name. For instance, the following declares the
system `simple`, where each tag can only be executed once for each identity.

.. squirreltop::  in

   system [simple] ((!_j reader) | (!_i tag(i))).


Reachability properties
-------------------------

We consider reachability formulas, that is, properties that talk
about what is possible or not for all traces.
In **Squirrel**, we express such formulas in a first order logic,
and call them :term:`local formulas <local formula>`.

In this logic, terms can be of type :g:`message`, :g:`boolean`,
:g:`index` and :g:`timestamp`.  The logic lets us prove that formulas are
true for all possible traces of the protocol, and for all possible
values of the variables given a trace.

For instance, a timestamp variable `t` allows to talk about a given
point inside a trace. `t` will intuitively have to take the value of
some concrete action, *e.g.*, `T(i)` or `R(j)` in our case.


Macros
++++++

To discuss about the value of the output performed at some timestamp, we use macros:

 * :g:`input@t` is the value given as input by the attacker to the action at `t`;
 * :g:`output@t` is the output performed by the action at `t`;
 * :g:`cond@t` is the executability condition of the action at `t`;
 * :g:`frame@t` is the sequence of all previous outputs up to `t`;
 * :g:`exec@t` is the conjunction of all executability conditions up to `t`.

Formulas
++++++++

It is then possible to write formulas that capture properties
satisfied by all executions of the protocol. For instance, the
following formula describes that the executability execution of the
reader in fact implies some authentication property. More precisely,
there must exist an action :g:`T(i,k)` that was executed before the
reader, and such the input of the reader corresponds to the name of
:g:`T(i,k)`.

.. squirreltop::  all

   lemma wa :
     forall (i:index, j:index),
     happens(R(j,i)) =>
        cond@R(j,i) =>
            exists (k:index),
                 T(i,k) <= R(j,i) && fst(input@R(j,i)) = nT(i,k).


We write below the simple proof of this statement. The high-level
idea of the proof is to use the **EUF** cryptographic axiom:
only the tag `T(i,k)` can compute `h(nT(i,k),key(i))` because the
secret key is not known by the attacker. Therefore, any message
accepted by the reader must come from a tag that has played before.
The converse implication is trivial, because any honest tag output is
accepted by the reader.

Once inside a proof context, delimited by `Proof.` and `Qed.`, it is
possible to display the list of available tactics by typing `help.`, and
details about any tactic with `help tacticname.`

We now start the proof.

.. squirreltop::  all

   Proof.

After the :g:`Proof` command, **Squirrel** displays the current
judgement. It contains the number of goals that remain to be proved
(one at first, but additional subgoals may be created by tactics), the system we are
working in, and the formula to be proved.
   
.. squirreltop::  all
		  
     intro i j Hh Hc.

We have performed an introduction with the :tacn:`intro` tactic. This
pushes universal quantification inside the judgment context, where
the universally quantified variables become free variables. This allows us
to then push the left-hand side of the implications as hypotheses of
the judgment, that we can then reason on. The free variables and
assumptions are named according to the identifiers given as parameters to :tacn:`intro`.

.. squirreltop::  all
		  
     expand cond.

After introducing the hypotheses and expanding the executability
condition of :g:`R`, we get an equality between a hash and some other
term :g:`snd (input@R(j, i))`. We then use the unforgeability of the
hash function, the **EUF** assumption, to get that the hashed value
:g:`fst (input@R(j, i))` must be equal to some honestly hashed value
in :g:`snd (input@R(j, i))`, since the key :g:`key` is secret. All
honestly hashes are produced by the tag, which will then conclude our
proof. This cryptographic axiom is applied thanks to the :tacn:`euf`
tactic.
     
.. squirreltop::  all
   
     euf Hc.

To conclude, we just have to use the :g:`k` introduced by the
:tacn:`euf` tactic as a witness for the existential :g:`k` we have to
find.
     
.. squirreltop::  all
		  
     intro [k _].
     by exists k.
   Qed.


Equivalence properties
----------------------

More complex properties based on equivalence can be
expressed. Intuitively, two processes are equivalent if the attacker
cannot know whether it is interacting with one or the other. This is a
generic security property used in the computational model to prove
many distinct flavours of security.

We can declare in **Squirrel** two variants of a protocol at once using
the :g:`diff(t1,t2)` operator. A process containing diff-terms is
called a bi-process, as it can lead to two distinct processes when
projecting on the left or the right of the diff. This allows to easily
model some security properties.

For instance, we can declare a bi-process :g:`tagD`, where
on one side each tag may be called many times and always use
there own key, while on the right side, we in
fact use a new fresh independent key every time a tag is called.
The left-hand side of the process can be seen as the real world,
while the right-hand side is an idealised world where a new tag is used each time.
Proving that these two worlds are equivalent will establish
that tags cannot be tracked.

.. squirreltop::  all
		  
   name key': index * index -> message

   process tagD(i:index,k:index) =
     new nT;
     out(cT, <nT, h(nT,diff(key(i),key'(i,k)))>).

   process readerD(j:index) =
     in(cT,x);
     if exists (i,k:index), snd(x) = h(fst(x),diff(key(i),key'(i,k))) then
       out(cR,ok)
     else
       out(cR,ko)

   system [BasicHash] ((!_j R: readerD(j)) | (!_i !_k T: tagD(i,k))).

Importantly, reachability formulas can be expressed and proved
directly on bi-systems. We can for instance write a variant of the
previous proof directly on the bi-system:

.. squirreltop:: all
		 
   lemma [BasicHash] wa_R :
     forall (tau:timestamp),
       happens(tau) =>
       ((exists (i,k:index),
          snd(input@tau) = h(fst(input@tau),diff(key(i),key'(i,k))))
        <=>
        (exists (i,k:index), T(i,k) < tau &&
          fst(output@T(i,k)) = fst(input@tau) &&
          snd(output@T(i,k)) = snd(input@tau))).

The idea of the proof is similar, except that we prove here a
logical equivalence instead of an implication.
    
.. squirreltop:: all
		 
   Proof.
     intro tau Hap.

We have to prove two implications (:g:`<=>`): we thus split the proof
in two parts. We now have two different goals to prove.


.. squirreltop:: all
		 
     split; intro [i k Meq].

For the first implication (:g:`=>`), we actually consider separately
the real system (left) and the ideal system (right).
     
.. squirreltop:: all
		 
     project.

The proof is very similar on both sides, and relies on the :tacn:`euf`
tactic.  Applying the :tacn:`euf` tactic on the `Meq` hypothesis
generates a new hypothesis stating that `fst(input@R(j))` must be
equal to some message that has already been hashed before.  The only
possibility is that this hash comes from the output of a tag that has
played before (thus the new hypothesis on timestamps).

.. squirreltop:: all

     euf Meq.
     intro [k0 _].
     by exists i,k0.

The right side of the proof is very similar. 
     
.. squirreltop:: all
   
     euf Meq => *.
     by exists i,k.

We use here the notation :g:`euf Meq => *`, which is a shortcut for
:g:`euf Meq; intro *`, the :g:`*` performing as many introductions
as possible, with automatic naming of variables and hypotheses.

For the second implication (:g:`<=`), the conclusion of the goal can
directly be obtained from the hypotheses.
     
.. squirreltop:: all
   
     by exists i,k.
   Qed.
		 



We now prove an equivalence property expressing the unlinkability of the
protocol. This property is expressed by the logical formula :g:`forall
t:timestamp, [happens(t)] -> equiv(frame@t)` where :g:`frame@t` is
actually a bi-frame. It states that for any trace (the quantification
is implicit over all traces), at any point that happens in the trace,
the two frames (derived by projecting the diff operator) are equivalent. Square
brackets contain local formulas, and such a formula mixing both local
formulas and equivalences is called a :term:`global formula`.

Here, we will have to prove that the left projection of :g:`frame@t` (*i.e.*
the real system) is indistinguishable from the right projection of
:g:`frame@t` (*i.e.* the ideal system).

As this goal is a frequent one, a shortcut allows declaring this goal
without writing the full formula, using the keyword :g:`equiv`.

.. squirreltop:: all

   equiv [BasicHash] unlinkability.
   Proof.

An equivalence judgment contains the list of hypotheses, as
before. The conclusion is however different to the reachability
case. Now, we have a numbered list of diff-terms, and we must prove that
the left projection and the right projection of this list are
indistinguishable. We refer to this sequence of diff terms as the
biframe of the goal.
		    
The high-level idea of the proof is as follows:

* if :g:`t` corresponds to a reader's action, we show that the outcome of the
  conditional is the same on both sides and that this outcome only depends
  on information already available to the attacker;
* if :g:`t` corresponds to a tag's action, we show that the new message added
  in the frame (*i.e.* the tag's output) does not give any information
  that helps the attacker distinguish the real system from the ideal one.
  Indeed, hashes can intuitively be seen as fresh names thanks to the **PRF**
  cryptographic axiom.

The proof is done by induction over the timestamp :g:`t`.  The
:tacn:`induction` tactic also automatically introduces a case analysis over
all possible values for :g:`t`.  The first case, where :g:`t =
init` corresponds to the initial point of the execution trace, before
any protocol action has happened. That case is trivial, we directly close it with
:tacn:`auto`.  The other cases correspond to the 3 different actions
of the protocol.


.. squirreltop:: all
		 
   induction t.
   auto.

  
For the case where :g:`t = R2(j)`, we start by expanding the macros
and splitting the pairs. Splitting the pairs is done by using the
:tacn:`fa` tactic, which when applied to all pairs thanks to the
pattern :g:`!<_,_>` splits a bi-frame element containing a pair into
two biframe elements, containing the the two components.

.. squirreltop:: all
		 
   expand frame, exec, output.   
   fa !<_,_>.

Using the previously proved authentication goal :g:`wa_R`, we replace
the formula :g:`cond@R2(j)` with an equivalent formula, which states
that a tag :g:`T(i,k)` has played before and that the output of
this tag is equal to the message input by the reader. This is one of the
strength of **Squirrel**: we can finely reuse previously proved goals to
simplify a current goal. Here, we can see the :g:`wa_R` lemma as a
rewriting rule over boolean formulas, and so we use the :tacn:`rewrite`
tactic.


.. squirreltop:: all
		 	
    rewrite /cond (wa_R (R2 j)) //.

We are now able to remove this formula from the frame because the
attacker is able to compute it using information obtained in the
past. Indeed, each of its elements is already available in
:g:`frame@pred(R2(j))`. This is done by the :tacn:`deduce` tactic.
   
.. squirreltop:: all
		 	
    by deduce 1.
    
The case where :g:`t = R1(j)` is similar to the previous one.

.. squirreltop:: all
		       
  expand frame, exec, output.
  fa !<_,_>.
  rewrite /cond (wa_R (R1 j)) //.
  by deduce 1.

Finally, for the case where :g:`t = T(i,k)`, we similarly start by expanding the
macros and splitting the pairs.

.. squirreltop:: all
		   
    expand frame, exec, cond, output.
    fa !<_,_>, if _ then _, <_,_>.
    
We now apply the :tacn:`prf` tactic, in order to replace the hash with a fresh
name. This creates a new subgoal, asking to prove that the hashed value
has never been hased before.
 
.. squirreltop:: all
		 	
    prf 2.
    
Several conjuncts must now be proved, the same tactic can be used on
all of them. Here are a few representative cases:

  - In one case, :g:`nT(i,k)` cannot occur in :g:`input@R2(j)`
    because :g:`R2(j) < T(i,k)`.
  - In another case, :g:`nT(i,k) = nT(i0,k0)` implies that :g:`i=i0` and :g:`k=k0`,
    contradicting :g:`T(i0,k0)<T(i,k)`.

In both cases, the reasoning is performed by the :tacn:`fresh` tactic on the
message equality hypothesis :g:`Meq`, whose negation was initially to be
proved. To be able to use (:tacn:`split` and) :tacn:`fresh`, we first project the
goal onto on the left projection and one goal for the right projection of the initial bi-system. 

.. squirreltop:: all
		   
      repeat split; intro *; by fresh Meq.
      repeat split; intro *; by fresh Meq.


We have now replaced the hash by a fresh name occurring nowhere else,
so we can remove it using the :tacn:`fresh` tactic.

.. squirreltop:: all
		 	
    fresh 2; 1:auto.
      
We can also remove the name :g:`nT(i,k)`, and conclude (automatically) by the induction
hypothesis.
	
.. squirreltop:: all
		 	
    by fresh 1.
    Qed.
