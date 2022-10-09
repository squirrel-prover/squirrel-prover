(*
# Protocol modelling

## Messages

Messages exchanged by a protocol are modelled using _terms_.

Concretely, a message is either

 * a name `n` used to model a random sampling;
 * the application of a function `f(m_1,...,m_k)`.


In __Squirrel__, a function symbol without any assumption can be defined with:

```*)
abstract ok : message
abstract ko : message
abstract f1 : message -> message
abstract f2 : message * message -> message.

(*```

`ok` and `ko` are constants, and `f1` is a function that expects a message, and
then return a message. `f2` is then a function symbol of arity two, and function
symbols of any arity can be defined this way.


A name `n` allows to model secret keys, or some random challenge. As we wish to
be able to refer to an unbounded number of session, we allow names to be
indexed, each value of the index yielding a fresh independent random. We denote
by `n[i]` an indexed name, with variable `i` as an index. Names can be indexed
by any number of indices.

In the tool, one can declare names and indexed names with the following.

```*)
name n : message
name n1 : index -> message
name n2 : index * index -> message.

(*```

 To model a setting where multiple people each have their own secret key,
one could declare an indexed name as follows.

```*)
name key : index -> message.

(*```

## Cryptographic assumptions

Symbol functions can be defined as being an encryption, or a hash function, or a
signature, or... The tool will then assume that such functions satisfy some
classical cryptographic assumptions.

The possible sorts and corresponding assumptions are:

 * encryption,  __CCA1__ & __INT-CTXT__, symmetric and asymmetric
 * signatures, __EUF-CMA__
 * hash functions, __PRF__, and thus __EUF-CMA__, __CR__

Each are declared in the following way.

```*)
signature sign,checksign,pk
hash h
senc enc,dec
aenc asenc,asdec,aspk.

(*```

## Protocols

Protocols are described inside a pi-calculus. It is based on the following constructs:

 *  `new n` id used to instantiate a fresh name;
 * `out(c,m)` is used to send the term `m` over the channel `c`;
 * `in(c,x)` is used to receive some value from channel `c`, bound to the variable `x`;
 * `act; P` correspond to the sequential composition of action `act` with process `P`;
 ... TODO

As an example, we use a small _RFID_ based protocol, with a tag and a reader,
called the basic hash protocol:

* Mayla Brusò, Kostas Chatzikokolakis, and Jerry den Hartog. _Formal
Verification of Privacy for RFID Systems_. pages 75–88, July 2010.

```
T --> R : <nT, h(nT,kT)>
R --> T : ok
```

We first declare the channels used by the protocol. Remark that channels are
mostly byproducts of the theory, and do not play a big role.

```*)
channel cT
channel cR.

(*```

We then define a first process of a protocol, which may correspond to
multiple identies, and thus depend on some index variable `i`.

```*)
process tag(i:index) =
  new nT;
  T : out(cT, <nT, h(nT,key(i))>).

(*```

We can then declare the reader.

```*)
process reader(j:index) =
  in(cT,x);
  try find i such that snd(x) = h(fst(x),key(i)) in
   R : out(cR,ok)
  else
    out(cR,ko).
(*```

And we finally declare the final system. We instantiate multiple copies
of the reader, and for each value `i`, we also instantiate multilpe copies of
`tag(i)` with the replicaiton over `k`.

```*)
system ((!_j reader(j)) | (!_i !_k tag(i))).

(*```

A system declared this way is given the name `default`. Other systems can
be defined and given an epxlicit name. For instance, the following declare the
system `simple`, where each tag can only be executed once for each identity.

```*)
system [simple] ((!_j reader(j)) | (!_i tag(i))).

(*```

# Reachability properties

We express reachabilities formulas inside a first-order logic. In this logic, terms can be of type `message`, `boolean`, `index` and `timestamp`.
The logic proves that formulas are true for all possible traces of the protocol, and for all possible values of the variable given this trace/

For instance, a timestamp variable `t` allows to talk about a given point inside a trace. `t` will intuitively have to take the value of some concrete action, e.g., `T(i)` or `R(j)` in our example.

## Macros

To discuss about the value of the output performed at some timestamp, we use macros:

 * `input@t` is the value given as input by the attacker to the action at t;
 * `output@t` is the output performed by action at t;
 * `cond@t` is the executability condition at t;
 * `frame@t` is the sequence of all previous outputs up to t;
 * `exec@t` is the conjonction of all executability conditions up to t.

## Formulas

It is then possible to write formulas that capture properties satisfied by all
executions of the protocol. For instance, the following formula describes that
the executability execution of the reader in fact implies some authentication
property, in the sense that there must exists an action T(i,k) that was executed
before the reader, and such the input of the reader corresonds to the name of
T(i,k).

```*)

goal wa :
  forall (i:index, j:index),
  happens(R(j,i)) =>
     cond@R(j,i) =>
         exists (k:index),
              T(i,k) <= R(j,i) && fst(input@R(j,i)) = nT(i,k).
(*```

We write bellow the simple proof of this statement. Once inside a proof context, delimited by `Proof.` and `Qed.`, it is possible to get the list of available tactics by typing `help.`, and details about any tactic with `help tacticname.`

```*)
Proof.
  help.
  help intro.
  intro i j Hh Hc.
  expand cond.
  euf Hc.
  intro *; by exists k.
Qed.

(*```
# Indistinguishability properties

WIP

*)
