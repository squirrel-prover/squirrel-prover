# Minimal makefile for Sphinx documentation
#

# You can set these variables from the command line, and also
# from the environment for the first two.
SPHINXOPTS    ?=
SPHINXBUILD  ?= sphinx-build
SOURCEDIR     = source
BUILDDIR      = build

SHELL := /bin/bash

# Put it first so that "make" without argument is like "make help".
help:
	@echo "Checking for python3 venv."
	@if [ -d ".venv" ]; then \
		source .venv/bin/activate && $(SPHINXBUILD) -M help "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O); \
	else \
		echo "No python3 venv found, see the README in case of failure"; \
		$(SPHINXBUILD) -M help "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O); \
	fi

.PHONY: help Makefile

# Catch-all target: route all unknown targets to Sphinx using the new
# "make mode" option.  $(O) is meant as a shortcut for $(SPHINXOPTS).
%: Makefile 
	@if [ -d ".venv" ]; then \
		source .venv/bin/activate && $(SPHINXBUILD) -M $@ "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O); \
	else \
		echo "No python3 venv found, see the README in case of failure"; \
		$(SPHINXBUILD) -M $@ "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O); \
	fi


# This remove comments from tutorial so that it can be used as is 
# in the documentation TODO add directives squirreltop
tutorial:
	cp ../../examples/basic-tutorial/tutorial.sp ./source/tutorial.md
	sed -i 's/(\*//g' ./source/tutorial.md
	sed -i 's/\*)//g' ./source/tutorial.md
