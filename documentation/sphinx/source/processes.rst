.. _section-processes:

==========
Processes
==========

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

The body of a process is defined with sequential or parallel composition of commands,conditionals, find constructs, replication or process calls.

..  prodn::
    process_id ::= @identifier
    alias ::= @identifier
    proc ::= command; proc
        | proc | proc
	| if term then proc else proc
	| try find @binders such that @term in proc else proc
	| let @identifier = term in proc
	| !_@identifier proc
	| @process_id[({*, @term})]
	| @alias : proc
    process_decl ::= process @process_id[({*, @binders})] = @proc	

The construct :g:`A : proc` does not have any impact on the semantics of the model: it is only used to give an alias to this location in the process.	


Finally, a system is defined by a main process:

.. prodn::
   system_decl ::= system [@system_id] @process

.. todo::
   - describe the syntax and semantics of processes,
   - the implicit declaration of names and macros,
   - the role of diff operators,
   - and how processes lead to systems,
   - our flavour of diff-equivalence.
