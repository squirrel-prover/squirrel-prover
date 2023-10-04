.. _tutorial:

.. Gentle introduction to Squirrel

This tutorial provides a very quick introduction to the main concepts
of **Squirrel**. It can be used to ease its discovery and to get an
intuitive grasp of the multiple concepts by going through a concrete
example. The reference manual provides a more extensive presentation
of all the concepts.

In many cases, the concept introduced here are also direct clickable
references to the more extensive presentation in the reference manual.

Protocol modelling
--------------------

Squirrel allows performing proofs of security for communication
protocols relying on cryptography. It works within a high-order logic,
and a first step is to be able to model all the components of a
protocol inside a logic.

Messages
++++++++

Messages computed by a protocol and sent over the
network are modelled using :ref:`terms <term>`.

Concretely, a term is built from

 * a name :g:`n` used to model a random sampling;
 * applications of functions :g:`f(m_1,...,m_k)`.

This allows effectively modeling any computation, as one
can have function symbols modeling any sort of computations, from
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
then return a message. `f2` is then a function symbol of arity two, and function
symbols of any arity can be defined this way.


A name `n` typically allows modeling secret keys or nounces. As we wish to
be able to refer to an unbounded number of sessions, we allow names to be
indexed, each value of the index yielding a fresh independent random value. We denote
by `n[i]` an indexed name, with variable `i` as an index. Names can be indexed
by any number of indices.

In the tool, one can declare names and indexed names with the following.

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

A proof over such model would then apply to any concrete
implementation in which :g:`ok` and :g:`ko` are given two concrete
values as long as those two values are distinct.
   
Axioms are formulas in a high-order logic, for instance allowing free
variables, universal and existential quantification, implications,
etc. Here, we define the axiom as true over :g:`any` protocol.

Another axiom that could be useful to prove the security of a protocol
is for instance that :g:`ko` can never be equal to any pair
:g:`<x,y>`.

.. squirreltop::  in
		  
   axiom [any] ok_not_pair (x,y:message): <x,y> <> fail.


Going back to the name declaration, if we now display the **Squirrel**
output after a declaration, we see the following:

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

Some possible primitives and corresponding assumptions are:

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

Protocols are described inside a pi-calculus as :ref:`processes <section-processes>`. It is based on the following constructs:

 *  :g:`new n` id used to declare a fresh name; (this is optional, and equivalent to declaring the names as seen before)
 * :g:`out(c,m)` is used to send the term `m` over the channel `c`;
 * :g:`in(c,x)` is used to receive some value from channel `c`, bound to the variable `x`;
 * :g:`act; P` correspond to the sequential composition of action `act` with process `P`;
 * :g:`process name(vars) = ...` allows declaring a process with a name, in which case using `name(vars)` inside another process unfold the process definition;
 * :g:`P | Q` is a parallel composition of two processes;
 * :g:`if phi then P else Q` is a conditional branching;  
 * :g:`try find vars such that phi in P else Q` is a global lookup over indices, it can be seen as a lookup inside a database.   

 

As an example, we use a small *RFID* based protocol, with a tag and a reader,
called the basic hash protocol :cite:`bruso2010formal`.



.. example:: Basic Hash
	     
   T --> R : <nT, h(nT,kT)>
   
   R --> T : ok

Here, a tag :g:`T` sends to the reader :g:`R` a fresh challenge
:g:`nT`, authenticated via a MAC over the challenge using the key tag
:g:`kT`. Each tag has a distinct :g:`kT`, and the reader has a
database containing all of them.
   

We first declare the channels used by the protocol. Remark that channels are
mostly byproducts of the theory, and do not play a big role.

.. squirreltop::  in

   channel cT
   channel cR.


We then define the first process for the tags, which may correspond to
multiple identies, and thus depend on some index variable `i`.

.. squirreltop::  in

   process tag(i:index) =
     new nT;
     T : out(cT, <nT, h(nT,key(i))>).


We can then declare the reader.

.. squirreltop::  in

   process reader =
     in(cT,x);
     try find i such that snd(x) = h(fst(x),key(i)) in
       R : out(cR,ok)
     else
      R1 : out(cR,ko).

And we finally declare the final system. We instantiate multiple copies
of the reader, and for each value `i`, we also instantiate multiple copies of
:g:`tag(i)` with the replication over `k`.

.. squirreltop::  all

   system ((!_j reader) | (!_i !_k tag(i))).


We see that when declaring such a system, in the final system after
processing, all outputs have been given name, each output then
corresponds to a possible action that can be triggered by the
attacker. Here, the possible actions are :g:`(init,R,R1,T)`, and
many axioms are created, corresponding to the fact that for instance
actions :g:`R1` and :g:`R` are mutually exclusive as both
correspond to exclusive branches; this is the
:g:`mutex_default_R1_R` axiom, stating that for any possible
execution, one of the two actions must not happen in the trace.
   
A system declared this way is given the name `default`. Other systems can
be defined and given an explicit name. For instance, the following declare the
system `simple`, where each tag can only be executed once for each identity.

.. squirreltop::  in

   system [simple] ((!_j reader) | (!_i tag(i))).


Reachability properties
-------------------------

We express reachabilities formulas, that is, properties that talk
about what is possible or not for all traces, inside a first-order
logic. In **Squirrel**, such formulas are formally called
:term:`local formulas <local formula>`.

In this logic, terms can be of type :g:`message`, :g:`boolean`,
:g:`index` and :g:`timestamp`.  The logic proves that formulas are
true for all possible traces of the protocol, and for all possible
values of the variable given this trace.

For instance, a timestamp variable `t` allows talking about a given
point inside a trace. `t` will intuitively have to take the value of
some concrete action, e.g., `T(i)` or `R(j)` in our example.

Macros
++++++

To discuss about the value of the output performed at some timestamp, we use macros:

 * :g:`input@t` is the value given as input by the attacker to the action at t;
 * :g:`output@t` is the output performed by action at t;
 * :g:`cond@t` is the executability condition at t;
 * :g:`frame@t` is the sequence of all previous outputs up to t;
 * :g:`exec@t` is the conjunction of all executability conditions up to t.

Formulas
++++++++

It is then possible to write formulas that capture properties
satisfied by all executions of the protocol. For instance, the
following formula describes that the executability execution of the
reader in fact implies some authentication property, in the sense that
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


We write bellow the simple proof of this statement.  The high-level
idea of the proof is to use the EUF cryptographic axiom:
only the tag `T(i,k)` can compute `h(nT(i,k),key(i))` because the
secret key is not known by the attacker.  Therefore, any message
accepted by the reader must come from a tag that has played before.
The converse implication is trivial because any honest tag output is
accepted by the reader.

Once inside a proof context, delimited by `Proof.` and `Qed.`, it is
possible to get the list of available tactics by typing `help.`, and
details about any tactic with `help tacticname.`

We now start the proof.

.. squirreltop::  all

   Proof.

After the :g:`Proof` command, **Squirrel** displays the current
judgement. It contains the number of goal that remains to be proved
(here, one, but subogals may be created by tactics), the system we are
working in, and the formula to be proved.
   
.. squirreltop::  all
		  
     intro i j Hh Hc.

We have performed an introduction with the :tacn:`intro` tactic. This
pushes universal quantifications inside the judgment context, where
the universal quantified variable become free variable. This allows us
to then push the left-hand side of the implications as hypothesis of
the judgment, that we can then reason on. The free variables and
assumptions are named according to the names passed as argument.

.. squirreltop::  all
		  
     expand cond.

After introducing the hypothesis and expanding the executability
condition of :g:`R`, we get an equality between a hash and some other
term :g:`snd (input@R(j, i))`. We then use the unforgeability of the
hash function, the EUF assumption, to get that the hashed value
:g:`fst (input@R(j, i))` must be equal to some honestly hashed value
in :g:`snd (input@R(j, i))`, as the key :g:`key` is secret. All
honestly hash are produced by the tag, which will then conclude our
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
cannot know whether it is interacting with one or another. This is a
generic security property used in the computational model to prove
many distinct flavours of security.

We can declare in **Squirrel** two variants of a protocol at once using
the :g:`diff(t1,t2)` operator. A process containing diff-terms is
called a bi-process, as it can lead to two distinct processes when
projecting on the left or the right of the diff. This allows to easily
model some security properties.

For instance, we can declare a bi-process :g:`tagD` that models the
fact the on one side each tag may be called many times and always use
there own key, this is the real world, while on the right side, we in
fact use a new fresh independent key every time a tag is called. If
those two world are equivalent, then tags cannot be tracked.

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
directly on bi-systems. We can for instance do a variant of the
previous proof on the bi-system directly:

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

The idea of the proof is similar, except that we prove here an
equivalence instead of an implication.
    
.. squirreltop:: all
		 
   Proof.
     intro tau Hap.

We have to prove two implications (`<=>`): we thus split the proof
in two parts. We now have two different goals to prove.


.. squirreltop:: all
		 
     split; intro [i k Meq].

For the first implication (=>), we actually prove it separately for
the real system (left) and the ideal system (right).
     
.. squirreltop:: all
		 
     project.

The proof is very similar on both sides and relies on the :tacn:`euf`
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
:g:`euf Meq; intro *`, the :g:`*` doing introduction with automatic
naming of variables and hypothesis.

For the second implication (<=), the conclusion of the goal can
directly be obtained from the hypotheses.
     
.. squirreltop:: all
   
     by exists i,k.
   Qed.
		 



We now prove an equivalence property expressing unlinkability of the
protocol. This property is expressed by the logical formula :g:`forall
t:timestamp, [happens(t)] -> equiv(frame@t)` where :g:`frame@t` is
actually a bi-frame. This state that for any trace (the quantification
is implicit over all traces), for any point that happens in the trace,
the two frames (based on the diff operator) are equivalent. Square
brackets contain local formulas, and such a formula mixing both local
formulas and equivalences is called a :term:`global formula`.

Here, we will have to prove that the left projection of :g:`frame@t` (*i.e.*
the real system) is indistinguishable from the right projection of
:g:`frame@t` (*i.e* the ideal system).

As this goal is a frequent one, a shortcut allows declaring this goal
without writing the full formula.

.. squirreltop:: all

   equiv [BasicHash] unlinkability.
   Proof.

An equivalence judgment contains the list of hypothesis, as
before. The conclusion is however different to the reachability
case. Now, we have a numbered list of diff-terms, we must prove that
for each of them, the left projection and the right projection are
indistinguishable. We refer to this sequence of diff terms as the
biframe of the goal.
		    
The high-level idea of the proof is as follows:

* if :g:`t` corresponds to a reader's action, we show that the outcome of the
  conditional is the same on both sides and that this outcome only depends
  on information already available to the attacker;
* if :g:`t` corresponds to a tag's action, we show that the new message added
  in the frame (_i.e._ the tag's output) does not give any information to
  the attacker to distinguish the real system from the ideal one since
  hashes can intuitively be seen as fresh names thanks to the PRF
  cryptographic axiom.

The proof is done by induction over the timestamp :g:`t`.  The
`induction` tactic also automatically introduces a case analysis over
all the possible values for :g:`t`.  The first case, where :g:`t =
init` corresponds to first point of the execution trace where no
protocol action happened, is trivial, we directly close it with
:tacn:`auto`.  The other cases correspond to the 3 different actions
of the protocol.


.. squirreltop:: all
		 
   induction t.
   auto.

  
For the case where :g:`t = R2(j)`, we start by expanding the macros
and splitting the pairs. Splitting the pairs is done by using the
:tacn:`fa` tactic, which when applied to all pairs thanks to the
pattern :g:`!<_,_>` splits a bi-frame element containing a pair into
two biframe elements for each element of the pair.

.. squirreltop:: all
		 
   expand frame, exec, output.   
   fa !<_,_>.

Using the authentication goal :g:`wa_R` previously proved, we replace
the formula :g:`cond@R2(j)` by an equivalent formula expressing the
fact that a tag :g:`T(i,k)` has played before and that the output of
this tag is the message inputted by the reader. This is one of the
strength of **Squirrel**, we can finely reuse previously proved goals to
simplify a current goal. Here, as we can see the :g:`wa_R` tactic as a
rewriting rule over boolean formulas, we use the :tacn:`rewrite`
tactic.


.. squirreltop:: all
		 	
    rewrite /cond (wa_R (R2 j)) //.

We are now able to remove this formula from the frame because the
attacker is able to compute it using information obtained in the
past. Indeed, each element of this formula is already available in
:g:`frame@pred(R2(j))`. This is done by the :tacn:`deduce` tactic.
   
.. squirreltop:: all
		 	
    by deduce 1.
    
In the case where :g:`t = R1(j)`, it is similar to the previous one.

.. squirreltop:: all
		       
  expand frame, exec, output.
  fa !<_,_>.
  rewrite /cond (wa_R (R1 j)) //.
  by deduce 1.

Finally, for the case where t = T(i,k), we start by expanding the
macros and splitting the pairs.

.. squirreltop:: all
		   
    expand frame, exec, cond, output.
    fa !<_,_>, if _ then _, <_,_>.
    
We now apply the :tacn:`prf` tactic, in order to replace the hash by a fresh
name, and creates a subgoal asking to prove that the hashed value is indeed fresh.
The goal is now to prove that this condition always evaluates to `true`.
 
.. squirreltop:: all
		 	
    prf 2.
    
Several conjuncts must now be proved, the same tactic can be used on
all of them. Here are representative cases:

  - In one case, :g:`nT(i,k)` cannot occur in :g:`input@R2(j)`
    because :g:`R2(j) < T(i,k)`.
  - In another case, :g:`nT(i,k) = nT(i0,k0)` implies that :g:`i=i0` and :g:`k=k0`,
    contradicting :g:`T(i0,k0)<T(i,k)`.

In both cases, the reasoning is performed by the fresh tactic on the
message equality hypothesis :g:`Meq` whose negation must initially be
proved.  To be able to use (split and) fresh, we first project the
goal into one goal for the left projection and one goal for the
right projection of the initial bi-system. 

.. squirreltop:: all
		   
      repeat split; intro *; by fresh Meq.
      repeat split; intro *; by fresh Meq.


We have now replaced the hash by a fresh name occurring nowhere else,
so we can remove it using the :tacn:`fresh` tactic.

.. squirreltop:: all
		 	
    fresh 2; 1:auto.
      
We can also remove the name :g:`nT(i,k)`, and conclude by induction
hypothesis.
	
.. squirreltop:: all
		 	
    by fresh 1.
    Qed.
