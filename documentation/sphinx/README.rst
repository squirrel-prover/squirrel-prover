SQUIRREL
========

This is the documentation tool for **Squirrel-prover**. It uses
**Sphinx** and a custom **Squirrel Domain** described here.

Dependences
-----------

This documention works for Python 3.13.7. 

First, create a python virtual env, from inside the `documentation/sphinx` folder.

.. code::
   cd documentation/sphinx
   python3 -m venv .venv
   source .venv/bin/activate


Here, your terminal should be running the python3 virtual env, you
can run `which pip3` to check this, with the expected output
`.../squirrel-prover/documentation/sphinx/.venv/bin/pip3`.

Then with pip :

.. code::
   pip3 install sphinx==9.1.0 sphinx_rtd_theme beautifulsoup4 sphinx-tabs readthedocs-sphinx-search\
   antlr4-python3-runtime==4.13.2 pexpect sphinxcontrib-bibtex myst-parser

The generated doc relies on syntax coloration through a fork of [fork
of `pygments`](https://github.com/squirrel-prover/pygments) including
a lexer for `squirrel` files. This repository must be pulled, and then
the corresponding python module installed with `pip3 install -e .`
inside the repository (while still inside the venv, so reruning
`source .venv/bin/activate` if needed).

Build
-----

``make html`` Build html version
``make latex`` Build latex version then go in ``build/latex/`` and
   type ``make`` to generate pdf.

The makefile should automatically load the previously created `venv`.
   
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

Rebuilding
----------



If the python package `antlr4-python3-runtime` needs to be upgraded to another version, note
that the files in `documentation/sphinx/source/ext/notations` need to be regenarated
with the exact same version of antlr4: install the corresponding
antlr4 version from e..,
https://www.cs.upc.edu/~cl/practica/install.html, and then run make in
the `notations` subdirectory.



Deployement
-----------

The documentation is manually deployed as part of the [Squirrel github
page](https://github.com/squirrel-prover/Squirrel-Prover.github.io).

The submodule for the squirrel-prover should be updated, and then
`make doc` inside the page updates it.

In addition, an independent check on the inria gitlab page is launched
for any commit with the tag `[doc]` inside its title.

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
