================================
Documenting Squirrel with Sphinx
================================

Squirrel's reference manual is written in `reStructuredText <http://www.sphinx-doc.org/en/master/usage/restructuredtext/basics.html>`_ (“reST”), and compiled with `Sphinx <http://www.sphinx-doc.org/en/master/>`_.
See `this README <../README.md>`_ for compilation instructions.

In addition to standard reST directives (a directive is similar to a LaTeX environment) and roles (a role is similar to a LaTeX command), the ``squirrelrst`` plugin loaded by the documentation uses a custom *Squirrel domain* — a set of Squirrel-specific directives that define *objects* like tactics, commands (vernacs), warnings, etc. —, some custom *directives*, and a few custom *roles*.  Finally, this manual uses a small DSL to describe tactic invocations and commands.

TODO list generation
====================

You can add a task in the todo list with this directive :

.. tabs::

   .. tab:: reStructuredText

      .. code-block:: rst

         .. todo::
            
            This is a task added into the todo list

         .. todo::
            
            This is an other task added into the todo list


   .. tab:: Produces

      .. todo::

         This is a task added into the todo list

      .. todo::
         
         This is an other task added into the todo list


The list can be displayed with :

.. tabs::

   .. tab:: reStructuredText

      .. code-block:: rst

         .. todolist::

   .. tab:: Produces

      .. todolist::


Squirrel objects
================

Our Squirrel domain defines multiple `objects`_.  Each object has a *signature* (think *type signature*), followed by an optional body (a description of that object).  The following example defines two objects: a variant of the ``cs`` tactic, and an error that it may raise.

.. tabs::

   .. tab:: reStructuredText

      .. code-block:: rst

         .. tacn:: cs @pattern {? in @natural}
            :name: case_study

            Performs case study on conditionals inside an equivalence.

            Without a specific target, :g:`cs phi` will project all conditionals
            on phi in the equivalence. With a specific target, :g:`cs phi in i`
            will only project conditionals in the i-th item of the equivalence.

             .. example:: 

                When proving an equivalence
                :g:`equiv(if phi then t1 else t2, if phi then u1 else u2)`
                invoking ``nosimpl cs phi`` results in two subgoals:
                :g:`equiv(phi, t1, u1)` and :g:`equiv(phi, t2, u2)`

            .. exn:: Argument of cs should match a boolean.
               :undocumented:

            .. exn:: Did not find any conditional to analyze.
               :undocumented:

   .. tab:: Produces

      .. tacn:: cs @pattern {? in @natural}
         :name: _ignore

         Performs case study on conditionals inside an equivalence.

         Without a specific target, :g:`cs phi` will project all conditionals
         on phi in the equivalence. With a specific target, :g:`cs phi in i`
         will only project conditionals in the i-th item of the equivalence.

          .. example::

             When proving an equivalence
             :g:`equiv(if phi then t1 else t2, if phi then u1 else u2)`
             invoking :g:`nosimpl cs phi` results in two subgoals:
             :g:`equiv(phi, t1, u1)` and :g:`equiv(phi, t2, u2)`.

         .. exn:: Argument of cs should match a boolean.
            :name: _ignore
            :undocumented:

         .. exn:: Did not find any conditional to analyze.
            :name: _ignore
            :undocumented:

Or :g:`fa` tactic :

.. tabs::

   .. tab:: reStructuredText

      .. code-block:: rst

         .. tacv:: _fa {?{| @natural | {+ @fa_arg}}}
            :name: _fa

            Apply the function application rule.

            Local sequent:
            When we have G => f(u) = f(v), produces the
            goal G => u=v. Produces as many subgoals as
            arugment of the head function symbol.
            Global sequent:

            To prove that a goal containing f(u1,...,un) is
            diff-equivalent, one can prove that the goal containing the
            sequence u1,...,un is diff-equivalent.

            .. exn:: improper arguments
               :undocumented:

   .. tab:: Produces

      .. tacv:: _fa {? {| @natural | {+ @fa_arg} } }
         :name: _fa

         Apply the function application rule.

         Local sequent:
         When we have G => f(u) = f(v), produces the
         goal G => u=v. Produces as many subgoals as
         arugment of the head function symbol.
         Global sequent:

         To prove that a goal containing f(u1,...,un) is
         diff-equivalent, one can prove that the goal containing the
         sequence u1,...,un is diff-equivalent.

         .. exn:: _improper arguments
            :undocumented:


Objects are automatically collected into indices, and can be linked to using the role version of the object's directive. For example, you could link to the tactic variant above using ``:tacv:`fa```, and to its exception using ``:exn:`imporper arguments```.

Names (link targets) are auto-generated for most simple objects, though they can always be overwritten using a ``:name:`` option, as shown above.

- Vernacs (commands) have their name set to the first word of their signature.  For example, the auto-generated name of :g:`system @id = @sys_descr with @sys_modifier` is ``system``, and a link to it would take the form ``:cmd:`system```.
- Vernac variants, tactic notations, and tactic variants do not have a default name.

Most objects should have a body (i.e. a block of indented text following the signature, called “contents” in Sphinx terms).  Undocumented objects should have the ``:undocumented:`` flag instead, as shown above.  When multiple objects have a single description, they can be grouped into a single object, like this (semicolons can be used to separate the names of the objects; names starting with ``_`` will be omitted from the indexes):

.. tabs::

   .. tab:: reStructuredText

      .. code-block:: rst

         .. cmdv:: _Lemma @ident {* @binder } : @type
                   _Remark @ident {* @binder } : @type
                   _kFact @ident {* @binder } : @type
                   _Corollary @ident {* @binder } : @type
                   _Proposition @ident {* @binder } : @type
            :name: _Lemma; _Remark; _Fact; _Corollary; _Proposition

            These commands are all synonyms of :n:`_Theorem @ident {* @binder } : type`.

   .. tab:: Produces

      .. cmdv:: _Lemma @ident {* @binder } : @type
                _Remark @ident {* @binder } : @type
                _Fact @ident {* @binder } : @type
                _Corollary @ident {* @binder } : @type
                _Proposition @ident {* @binder } : @type
         :name: _Lemma; _Remark; _Fact; _Corollary; _Proposition

         These commands are all synonyms of :n:`_Theorem @ident {* @binder } : type`.



Notations
---------

The signatures of most objects can be written using a succinct DSL for Squirrel notations (think regular expressions written with a Lispy syntax).  A typical signature might look like ``Hint Extern @natural {? @pattern} => @tactic``, which means that the ``Hint Extern`` command takes a number (``natural``), followed by an optional pattern, and a mandatory tactic.  The language has the following constructs (the full grammar is in `TacticNotations.g <_ext/notations/TacticNotations.g>`_):

``@…``
  A placeholder (``@ident``, ``@natural``, ``@tactic``\ ...)

``{? …}``
  an optional block

``{* …}``, ``{+ …}``
  an optional (``*``) or mandatory (``+``) block that can be repeated, with repetitions separated by spaces

``{*, …}``, ``{+, …}``
  an optional or mandatory repeatable block, with repetitions separated by commas

``{| … | … | … }``
  an alternative, indicating than one of multiple constructs can be used

``%{``, ``%}``, ``%|``
  an escaped character (rendered without the leading ``%``).  In most cases,
  escaping is not necessary.  In particular, the following expressions are
  all parsed as plain text, and do not need escaping: ``{ xyz }``, ``x |- y``.
  But the following escapes *are* needed: ``{| a b %| c | d }``, ``all: %{``.
  (We use ``%`` instead of the usual ``\`` because you'd have to type ``\``
  twice in your reStructuredText file.)

  For more details and corner cases, see `Advanced uses of notations`_ below.

..
   FIXME document the new subscript support

As an exercise, what do the following patterns mean?

.. tabs::

   .. tab:: Code

      .. code::

         _pattern {+, @term {? at {+ @natural}}}
         _generalize {+, @term at {+ @natural} as @ident}
         _fix @ident @natural with {+ (@ident {+ @binder} {? {struct @ident'}} : @type)}

   .. tab:: Result

      .. cmd:: _pattern {+, @term {? at {+ @natural}}}
         :undocumented:

      .. cmd:: _generalize {+, @term at {+ @natural} as @ident}
         :undocumented:

      .. cmd:: _fix @ident @natural with {+ (@ident {+ @binder} {? {struct @ident'}} : @type)}
         :undocumented:

Objects
-------

.. |black_nib|  unicode:: U+2712

Here is the list of all objects of the Squirrel domain (The symbol |black_nib| indicates an object whose signature can be written using the notations DSL):

``.. attr::`` |black_nib| An attribute.
    Example:

.. tabs::

   .. tab:: reStructuredText

      .. code-block:: rst

         .. attr:: _local

   .. tab:: Produces

      .. attr:: _local
         :undocumented:

``.. decl::`` |black_nib| A Squirrel declaration.
    Example:

.. tabs::

   .. tab:: reStructuredText

      .. code-block:: rst

       .. decl:: _lemma @string : @one_term {? ( {+, @syntax_modifier } ) } {? : @ident }

          This command is equivalent to

   .. tab:: Produces

    .. decl:: _lemma @string : @one_term {? ( {+, @syntax_modifier } ) } {? : @ident }

       This command is equivalent to



``.. cmd::`` |black_nib| A Squirrel command.
    Example:

.. tabs::

   .. tab:: reStructuredText

      .. code-block:: rst

       .. cmd:: _Infix @string := @one_term {? ( {+, @syntax_modifier } ) } {? : @ident }

          This command is equivalent to :n:`...`.

   .. tab:: Produces

    .. cmd:: _Infix @string := @one_term {? ( {+, @syntax_modifier } ) } {? : @ident }

       This command is equivalent to :n:`...`.


``.. cmdv::`` |black_nib| A variant of a Squirrel command.
    Example:

.. tabs::

   .. tab:: reStructuredText

      .. code-block:: rst

          .. cmd:: _Axiom @ident : @term.

             This command links :token:`term` to the name :token:`term` as its specification in
             the global environment. The fact asserted by :token:`term` is thus assumed as a
             postulate.

             .. cmdv:: _Parameter @ident : @term.

                This is equivalent to :n:`_Axiom @ident : @term`.

   .. tab:: produces

          .. cmd:: _Axiom @ident : @term.

             This command links :token:`term` to the name :token:`term` as its specification in
             the global environment. The fact asserted by :token:`term` is thus assumed as a
             postulate.

             .. cmdv:: _Parameter @ident : @term.

                This is equivalent to :n:`_Axiom @ident : @term`.

``.. exn::`` |black_nib| An error raised by a Squirrel command or tactic.
    This commonly appears nested in the ``.. tacn::`` that raises the
    exception.

.. tabs::

   .. tab:: reStructuredText

      .. code-block:: rst

          .. tacv:: _assert @form by @tactic

             This tactic applies :n:`@tactic` to solve the subgoals generated by
             ``assert``.

             .. exn:: Proof is not complete

                Raised if :n:`@tactic` does not fully solve the goal.

   .. tab:: produces

       .. tacv:: _assert @form by @tactic

          This tactic applies :n:`@tactic` to solve the subgoals generated by
          ``assert``.

          .. exn:: Proof is not complete

             Raised if :n:`@tactic` does not fully solve the goal.

``.. flag::`` |black_nib| A Squirrel flag (i.e. a boolean setting).

    **TODO** we rather call them options in the tool.

    Example:

.. tabs::

   .. tab:: reStructuredText

      .. code-block:: rst

       .. flag:: postQuantumSound

          Perform extra checks to ensure that results
          are sound wrt a quantum adversary.

   .. tab:: produces

       .. flag:: Nonrecursive Elimination Schemes

          Perform extra checks to ensure that results
          are sound wrt a quantum adversary.


``.. opt::`` |black_nib| A Squirrel option (a setting with non-boolean value, e.g. a string or numeric value).
    Example:

.. tabs::

   .. tab:: reStructuredText

      .. code-block:: rst

       .. opt:: _Hyps Limit @natural
          :name: _Hyps Limit

          Controls the maximum number of hypotheses displayed in goals after
          application of a tactic.

   .. tab:: produces

       .. opt:: _Hyps Limit @natural
          :name: _Hyps Limit

          Controls the maximum number of hypotheses displayed in goals after
          application of a tactic.

``.. prodn::`` A grammar production.
    Use ``.. prodn`` to document grammar productions instead of Sphinx
    `production lists
    <http://www.sphinx-doc.org/en/stable/markup/para.html#directive-productionlist>`_.

    prodn displays multiple productions together with alignment similar to ``.. productionlist``,
    however unlike ``.. productionlist``\ s, this directive accepts notation syntax.

    .. tabs::

      .. tab:: reStructuredText

         .. code-block:: rst

           .. prodn:: _occ_switch ::= { {? {| + | - } } {* @natural } }
                    _term += let: @pattern := @_term in @_term
                    | _second_production

      .. tab:: produces

           .. prodn:: _occ_switch ::= { {? {| + | - } } {* @natural } }
                       _term += let: @pattern := @_term in @_term
                       | _second_production

       The first line defines "occ_switch", which must be unique in the document.  The second
       references and expands the definition of "term", whose main definition is elsewhere
       in the document.  The third form is for continuing the
       definition of a nonterminal when it has multiple productions.  It leaves the first
       column in the output blank.

``.. table::`` |black_nib| A Squirrel table, i.e. a setting that is a set of values.
    Example:

    .. tabs::

      .. tab:: reStructuredText

         .. code-block:: rst

          .. table:: _Search Blacklist @string
             :name: _Search Blacklist

             Controls ...

      .. tab:: produces
      
          .. table:: _Search Blacklist @string
             :name: _Search Blacklist

             Controls ...

``.. tacn::`` |black_nib| A tactic, or a tactic notation.
    Example:

    .. tabs::

      .. tab:: reStructuredText

         .. code-block:: rst

          .. tacn:: _do @natural @expr

             :token:`expr` is evaluated to ``v`` which must be a tactic value...

      .. tab:: produces

          .. tacn:: _do @natural @expr

             :token:`expr` is evaluated to ``v`` which must be a tactic value...

``.. tacv::`` |black_nib| A variant of a tactic.
    Example:

    .. tabs::

      .. tab:: reStructuredText

         .. code-block:: rst

             .. tacn:: _fail

                This is the always-failing tactic: it does not solve any goal. It is
                useful for defining other tacticals since it can be caught by
                :tacn:`try`, :tacn:`repeat`, or the branching
                tacticals...

                .. tacv:: _fail @natural

                   The number is the failure level. If no level is specified, it
                   defaults to 0...

      .. tab:: produces

          .. tacn:: _fail

             This is the always-failing tactic: it does not solve any goal. It is
             useful for defining other tacticals since it can be caught by
             :tacn:`try`, :tacn:`repeat`, or the branching
             tacticals...

             .. tacv:: _fail @natural

                The number is the failure level. If no level is specified, it
                defaults to 0...

``.. tact::`` |black_nib| A tactic, or a tactic notation over trace.
    Example:

    .. tabs::

      .. tab:: reStructuredText

         .. code-block:: rst

           .. tact:: true

              Solves a goal when the conclusion is true.


      .. tab:: produces

           .. tact:: true

              Solves a goal when the conclusion is true.

``.. tace::`` |black_nib| A tactic, or a tactic notation over equivalence.
    Example:

    .. tabs::

      .. tab:: reStructuredText

         .. code-block:: rst

           .. tace:: deduce {? @natural }

              Invoking :g:`deduce i` removes the ith element from the biframe when it can be computed from the rest of the bi-frame. 
              :g:`deduce` try to deduce the biframe with the first equivalence in the hypotheses it finds.

      .. tab:: produces

           .. tace:: deduce {? @natural }

              Invoking :g:`deduce i` removes the ith element from the biframe when it can be computed from the rest of the bi-frame.
              :g:`deduce` try to deduce the biframe with the first equivalence in the hypotheses it finds.

``.. thm::`` A theorem.
    Example:

    .. tabs::

      .. tab:: reStructuredText

         .. code-block:: rst

             .. thm:: _Bound on the ceiling function

                Let :math:`p` be an integer and :math:`c` a rational constant. Then
                :math:`p \ge c \rightarrow p \ge \lceil{c}\rceil`.

      .. tab:: produces

          .. thm:: _Bound on the ceiling function

             Let :math:`p` be an integer and :math:`c` a rational constant. Then
             :math:`p \ge c \rightarrow p \ge \lceil{c}\rceil`.

``.. warn::`` |black_nib| An warning raised by a Squirrel command or tactic..
    Do not mistake this for ``.. warning::``; this directive is for warning
    messages produced by Squirrel.

    .. tabs::

      .. tab:: reStructuredText

         .. code-block:: rst

             .. warn:: _Ambiguous path

                When the coercion :token:`qualid` is added to the inheritance graph, non
                valid coercion paths are ignored.

      .. tab:: produces

          .. warn:: _Ambiguous path

             When the coercion :token:`qualid` is added to the inheritance graph, non
             valid coercion paths are ignored.


Squirrel directives
===================

In addition to the objects above, the ``squirreldomain`` Sphinx plugin defines the following directives:

``.. squirreltop::`` A reST directive to describe interactions with Squirrel.
 Usage::

    .. squirreltop:: options...

       code to be executed by Squirrel

 Example:

 .. tabs::

   .. tab:: reStructuredText

      .. code-block:: rst

         .. squirreltop:: all

            (* comment *)
            name n:message.
            name s:message.
            hash h.
            lemma [any] toto : true=>true.
            Proof.
               admit.
            Qed.
            print toto.

   .. tab:: produces

      .. squirreltop:: all

         (* comment *)
         name n:message.
         name s:message.
         hash h.
         lemma [any] toto : true=>true.
         Proof.
            admit.
         Qed.
         print toto.

 The blank line after the directive is required.  If you begin a proof,
 use the ``abort`` option to reset squirrel for the next example.

 Here is a list of permissible options:

 - Display options (choose exactly one)

   - ``all``: Display input and output
   - ``in``: Display only input
   - ``out``: Display only output
   - ``none``: Display neither (useful for setup commands)

 - Behavior options

   - ``reset``: Send a ``Reset.`` command before running this block
   - ``abort``: Send an ``Abort.`` command after running this block (leaves all pending proofs if any)

 ``squirreltop``\ 's state is preserved across consecutive ``.. squirreltop::`` blocks
 of the same document (``squirrelrst`` creates a single ``squirreltop`` process per
 reST source file).  Use the ``reset`` option to reset Squirrel's state.

 Example:

 .. tabs::

   .. tab:: reStructuredText

      .. code-block:: rst

         .. squirreltop:: abort all

            lemma [any] tutu : true=>true.
            Proof.

         .. squirreltop:: all

            print tutu.
            print toto.

         .. squirreltop:: reset all

            print toto.

   .. tab:: produces

         .. squirreltop:: abort all

            lemma [any] tutu : true=>true.
            Proof.

         .. squirreltop:: all

            print tutu.
            print toto.

         .. squirreltop:: reset all

            print toto.


``.. squirreldoc::`` A reST directive to display squirreltop-formatted source code.
    Usage::

       .. squirreldoc::

          squirrel code to highlight.

    .. tabs::

      .. tab:: reStructuredText

         .. code-block:: rst

             .. squirreldoc::

               name key  : index -> message
               name key' : index * index -> message

               (* Finally, we declare the channels used by the protocol. *)

               channel cT
               channel cR.

               process tag(i:index,k:index) =
                 new nT;
                 out(cT, <nT, h(nT,diff(key(i),key'(i,k)))>).

               process reader(j:index) =
                 in(cT,x);
                 if exists (i,k:index), snd(x) = h(fst(x),diff(key(i),key'(i,k))) then
                   out(cR,ok)
                 else
                   out(cR,ko).

               (* The system is finally defined by putting an unbounded number of tag and
                   reader processes in parallel.
                   This system is automatically translated to a set of actions:

                   * the initial action (`init`);
                   * one action for the tag (`T`);
                   * two actions for the reader, corresponding to the two branches of the
                     conditional (respectively `R` and `R1`). *)

               system [BasicHash] ((!_j R: reader(j)) | (!_i !_k T: tag(i,k))).

               lemma [BasicHash] wa_R :
                 forall (tau:timestamp),
                   happens(tau) =>
                   ((exists (i,k:index),
                      snd(input@tau) = h(fst(input@tau),diff(key(i),key'(i,k))))
                    <=>
                    (exists (i,k:index), T(i,k) < tau &&
                      fst(output@T(i,k)) = fst(input@tau) &&
                      snd(output@T(i,k)) = snd(input@tau))).

      .. tab:: produces

          .. squirreldoc::

               name key  : index -> message
               name key' : index * index -> message

               (* Finally, we declare the channels used by the protocol. *)

               channel cT
               channel cR.

               process tag(i:index,k:index) =
                 new nT;
                 out(cT, <nT, h(nT,diff(key(i),key'(i,k)))>).

               process reader(j:index) =
                 in(cT,x);
                 if exists (i,k:index), snd(x) = h(fst(x),diff(key(i),key'(i,k))) then
                   out(cR,ok)
                 else
                   out(cR,ko).

               (* The system is finally defined by putting an unbounded number of tag and
                   reader processes in parallel.
                   This system is automatically translated to a set of actions:

                   * the initial action (`init`);
                   * one action for the tag (`T`);
                   * two actions for the reader, corresponding to the two branches of the
                     conditional (respectively `R` and `R1`). *)

               system [BasicHash] ((!_j R: reader(j)) | (!_i !_k T: tag(i,k))).

               lemma [BasicHash] wa_R :
                 forall (tau:timestamp),
                   happens(tau) =>
                   ((exists (i,k:index),
                      snd(input@tau) = h(fst(input@tau),diff(key(i),key'(i,k))))
                    <=>
                    (exists (i,k:index), T(i,k) < tau &&
                      fst(output@T(i,k)) = fst(input@tau) &&
                      snd(output@T(i,k)) = snd(input@tau))).

This is not equivalent to ``.. squirreltop:: in`` since none of the given content is sent to ``squirreltop`` and then take time to be computed when doc is generated !


``.. example::`` A reST directive for examples.
    This behaves like a generic admonition; see
    http://docutils.sourceforge.net/docs/ref/rst/directives.html#generic-admonition
    for more details.

    Optionally, any text immediately following the ``.. example::`` header is
    used as the example's title.

    Example:

    .. tabs::

      .. tab:: reStructuredText

         .. code-block:: rst

             .. example:: Adding a hint to the automatic constraint solving procedure 

                The following adds ``not_true`` to the solver

                .. squirreldoc::

                  axiom [any] not_true : not(true) = false.
                  hint rewrite not_true.

      .. tab:: produces

          .. example:: Adding a hint to the automatic constraint solving procedure 

             The following adds ``not_true`` to the solver

             .. squirreldoc::

               axiom [any] not_true : not(true) = false.
               hint rewrite not_true.


Squirrel roles
==============

In addition to the objects and directives above, the ``squirrelrst`` Sphinx plugin defines the following roles:

``:g:`` Squirrel code.
    Use this for Squirrel snippets:

    .. tabs::

      .. tab:: reStructuredText

         .. code-block:: rst

             Apply tactics :g:`apply not_true; reflexivity` 
             or set options 
             :g:`set postQuantumSound=true.`
             or declare 
             :g:`(forall (a:'a), true) = true.`

      .. tab:: produces

             Apply tactics :g:`apply not_true; reflexivity` 
             or set options 
             :g:`set postQuantumSound=true.`
             or declare 
             :g:`(forall (a:'a), true) = true.`

``:n:`` Any text using the notation syntax (``@id``, ``{+, …}``, etc.).
    Use this to explain tactic equivalences.  For example, you might write
    this:

    .. tabs::

      .. tab:: reStructuredText

         .. code-block:: rst

          :n:`_generalize @term as @ident` is just like :n:`_generalize @term`, but
          it names the introduced hypothesis :token:`identifier`.

      .. tab:: produces

          :n:`_generalize @term as @ident` is just like :n:`_generalize @term`, but
          it names the introduced hypothesis :token:`identifier`.

    Note that this example also uses ``:token:``.  That's because ``identifier`` is
    defined in the Squirrel manual as a grammar production, and ``:token:``
    creates a link to that.  When referring to a placeholder that happens to be
    a grammar production, ``:token:`…``` is typically preferable to ``:n:`@…```.

``:gdef:`` Marks the definition of a glossary term inline in the text.
    Matching ``:term:`XXX``` constructs will link to it.
    Use the form ``:gdef:`text <term>``` to display "text"
    for the definition of "term", such as when
    "term" must be capitalized or plural for grammatical reasons.
    The term will also appear in the :ref:`glossary index <glossary_index>`.

    Examples:

    .. tabs::

      .. tab:: reStructuredText

         .. code-block:: rst

             A :gdef:`prime` number is divisible only by itself and 1.
             :gdef:`Composite <composite>` numbers are the non-prime numbers.

      .. tab:: produces

             A :gdef:`prime` number is divisible only by itself and 1.
             :gdef:`Composite <composite>` numbers are the non-prime numbers.

Common mistakes
===============

Improper nesting
----------------

DO
  .. code::

     .. cmd:: Foo @bar

        Foo the first instance of :token:`bar`\ s.

        .. cmdv:: Foo All

           Foo all the :token:`bar`\ s in
           the current context

DON'T
  .. code::

     .. cmd:: Foo @bar

     Foo the first instance of :token:`bar`\ s.

     .. cmdv:: Foo All

     Foo all the :token:`bar`\ s in
     the current context


Overusing ``:token:``
---------------------

DO
  .. code::

     This is equivalent to :n:`_Axiom @ident : @term`.

DON'T
  .. code::

     This is equivalent to ``_Axiom`` :token:`identifier` : :token:`term`.

..

DO
  .. code::

     :n:`power_tac @term [@ltac]`
       allows :tacn:`ring` and :tacn:`ring_simplify` to recognize...

DON'T
  .. code::

     power_tac :n:`@term` [:n:`@ltac`]
       allows :tacn:`ring` and :tacn:`ring_simplify` to recognize...

..

DO
  .. code::

     :n:`name={*; attr}`

DON'T
  .. code::

     ``name=``:n:`{*; attr}`

Omitting annotations
--------------------

DO
  .. code::

     .. tacv:: _assert @form as @simple_intropattern

DON'T
  .. code::

     .. tacv:: _assert form as simple_intropattern

Using the ``.. squirreltop::`` directive for syntax highlighting
----------------------------------------------------------------

DO
  .. code::

     A tactic of the form:

     .. squirreldoc::

        do [ t1 | … | tn ].

     is equivalent to the standard Ltac expression:

     .. squirreldoc::

        first [ t1 | … | tn ].

DON'T
  .. code::

     A tactic of the form:

     .. squirreltop:: in

        do [ t1 | … | tn ].

     is equivalent to the standard Ltac expression:

     .. squirreltop:: in

        first [ t1 | … | tn ].

Overusing plain quotes
----------------------

DO
  .. code::

     The :tacn:`refine` tactic can raise the :exn:`Invalid argument` exception.
     The term :g:`let a = 1 in a a` is ill-typed.

DON'T
  .. code::

     The ``refine`` tactic can raise the ``Invalid argument`` exception.
     The term ``let a = 1 in a a`` is ill-typed.

Plain quotes produce plain text, without highlighting or cross-references.

Overusing the ``example`` directive
-----------------------------------

DO
  .. code::

     Here is a useful axiom:

     .. squirreldoc::

        Axiom proof_irrelevance : forall (P : Prop) (x y : P), x=y.

DO
  .. code::

     .. example:: Using proof-irrelevance

        If you assume the axiom above

DON'T
  .. code::

     Here is a useful axiom:

     .. example::

        .. squirreldoc::

           Axiom proof_irrelevance : forall (P : Prop) (x y : P), x=y.

Tips and tricks
===============

Nested lemmas
-------------

The ``.. squirreltop::`` directive does *not* reset Squirrel after running its contents.  That is, the following will create two nested lemmas (which by default results in a failure)::

   .. squirreltop:: all

      lemma l1: 1 + 1 = 2.

   .. squirreltop:: all

      lemma l2: 2 + 2 <> 1.

Add either ``abort`` to the first block or ``reset`` to the second block to avoid nesting lemmas.

Abbreviations and macros
------------------------

Substitutions for specially-formatted names (like  ``|Cic|``, ``|Ltac|`` and ``|Latex|`` give |Cic|, |Ltac| and |Latex|), along with some useful LaTeX macros, are defined in a `separate file <refman-preamble.html>`_.  This file is automatically included in all manual pages.


Advanced uses of notations
--------------------------

  - Use `%` to escape grammar literal strings that are the same as metasyntax,
    such as ``{``, ``|``, ``}`` and ``{|``.  (While this is optional for
    ``|`` and ``{ ... }`` outside of ``{| ... }``, always using the escape
    requires less thought.)

  - Literals such as ``|-`` and ``||`` don't need to be escaped.

  - The literal ``%`` shouldn't be escaped.

  - Don't use the escape for a ``|`` separator in ``{*`` and ``{+``.  These
    should appear as ``{*|`` and ``{+|``.

