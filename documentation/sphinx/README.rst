SQUIRREL
========

This is the documentation tool for **Squirrel-prover**. It uses
**Sphinx** and a custom **Squirrel Domain** described here.

Dependences
-----------

First, install ``sphinx`` with ``apt install python3-sphinx`` (for debian
distributions)

Then with pip :

.. code::
   pip install sphinx_rtd_theme beautifulsoup4 sphinx-tabs\
   antlr4-python3-runtime==4.7.1 pexpect sphinxcontrib-bibtex myst-parser

You may want syntax coloration included in your generated
doc. There is a [fork of `pygments`](https://github.com/ThomasRuby/pygments) including a lexer for `squirrel`
files. You can install it but it's not necessary.

Build
-----

``make html`` Build html version
``make latex`` Build latex version then go in ``build/latex/`` and
   type ``make`` to generate pdf.

Help
----

Reference syntax:

.. tabs::

   .. tab:: reStructuredText

      .. code-block:: rst

         .. _My target:

         Explicit targets
         ~~~~~~~~~~~~~~~~

         Reference `My target`_.

   .. tab:: MyST (Markdown)

      .. code-block:: md

         (My_target)=
         ## Explicit targets

         Reference [](My_target).
