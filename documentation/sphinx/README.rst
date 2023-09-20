SQUIRREL
========

This is the documentation tool for **Squirrel-prover**. It uses
**Sphinx** and a custom **Squirrel Domain** described here.

Dependences
-----------

First, install ``sphinx``, for instance with `pip3 install -U sphinx` (see
sphinx's [documentation](https://www.sphinx-doc.org/en/master/usage/installation.html)
for alternatives). 

Then with pip :

.. code::
   pip3 install sphinx_rtd_theme beautifulsoup4 sphinx-tabs readthedocs-sphinx-search\
   antlr4-python3-runtime==4.7.1 pexpect sphinxcontrib-bibtex myst-parser

You may want syntax coloration included in your generated
doc. There is a [fork of `pygments`](https://github.com/ThomasRuby/pygments) including a lexer for `squirrel`
files. You can install it but it's not necessary.

Build
-----

``make html`` Build html version
``make latex`` Build latex version then go in ``build/latex/`` and
   type ``make`` to generate pdf.

Pygments
--------

To update pygments in the ci.
First connect to ci : 
```sh
ssh root@squirrel-slave.ci
```

Then connect as `ci` with `su ci`.
Go to the `pygments` directory in `home`.
Then,
```sh
git pull
python3.8 -m pip install -e .
```

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
