import sys
import os

sys.path.append(os.path.abspath("./ext"))

# -- Prolog ---------------------------------------------------------------

# Include substitution definitions in all files
with open("refman-preamble.rst") as s:
    rst_prolog = s.read()

# Configuration file for the Sphinx documentation builder.
#
# For the full list of built-in configuration values, see the documentation:
# https://www.sphinx-doc.org/en/master/usage/configuration.html

# -- Project information -----------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#project-information

project = 'Squirrel'
copyright = '2023, Squirrel developpers'
author = 'Squirrel developpers'
release = ''

# -- General configuration ---------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#general-configuration

extensions = [
    'sphinx.ext.ifconfig',
    'sphinx.ext.todo', # add todo:: directive
    'sphinx_tabs.tabs', # Needs `pip install sphinx-tabs`
    'myst_parser', # Needs `pip install myst-parser`
    'sphinxcontrib.bibtex',
    'squirreldomain',
    'sphinxcontrib.jquery',
    'sphinx_search.extension'
]

latex_additional_files = [
    "refman-preamble.sty",
]

# Add autodoc for ocaml ↓ But is not up to date (downgrade ocaml ?)
# extensions.append("sphinxcontrib.ocaml")
# primary_domain = "ocaml"
# Use the Squirrel domain
primary_domain = 'squirrel'
# ocaml_source_directories = ["../../../src"]
# ocaml_findlib_packages = ["batteries", "js_of_ocaml"]

source_suffix = {
    '.rst' : 'restructuredtext',
    '.txt' : 'restructuredtext',
    '.md' : 'markdown',
}

templates_path = ['_templates']

SUPPORTED_FORMATS = ["html", "latex"]

exclude_patterns = [
    'build',
    'Thumbs.db',
    '.DS_Store',
    'refman-preamble.rst',
] + ["*.{}.rst".format(fmt) for fmt in SUPPORTED_FORMATS]


# -- Options for HTML output -------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#options-for-html-output

# html_theme = 'alabaster'
html_theme = 'sphinx_rtd_theme'
# Needs `pip install sphinx_rtd_theme beautifulsoup4 \
# antlr4-python3-runtime==4.7.1 pexpect sphinxcontrib-bibtex`

# Add any paths that contain custom themes here, relative to this directory.
import sphinx_rtd_theme
html_theme_path = [sphinx_rtd_theme.get_html_theme_path()]

html_static_path = ['static']

html_theme_options = {
    'collapse_navigation': False,
    'navigation_depth': -1,
}
html_context = {
    'display_github': True,
    'github_user': 'squirrel-prover',
    'github_repo': 'squirrel-prover',
    'github_version': 'master',
    'conf_py_path': '/documentation/sphinx/source/'
}

# -- Options for LaTeX output ---------------------------------------------

###########################
# Set things up for XeTeX #
###########################

latex_elements = {
    'babel': '',
    'fontenc': '',
    'inputenc': '',
    'utf8extra': '',
    'cmappkg': '',
    'papersize': 'letterpaper',
    'classoptions': ',openany', # No blank pages
    'polyglossia': '\\usepackage{polyglossia}',
    'sphinxsetup': 'verbatimwithframe=false',
    'preamble': r"""
                 \usepackage{unicode-math}
                 \usepackage{microtype}

                 % Macro definitions
                 \usepackage{refman-preamble}

                 % Style definitions for notations
                 %\usepackage{squirrelqnotations}

                 % Style tweaks
                 \newcssclass{sigannot}{\textrm{#1:}}

                 % Silence 'LaTeX Warning: Command \nobreakspace invalid in math mode'
                 \everymath{\def\nobreakspace{\ }}
                 """
}

latex_engine = "xelatex"

# Cf. https://github.com/sphinx-doc/sphinx/issues/7015
latex_use_xindy = False

# navtree options
navtree_shift = True

# since sphinxcontrib-bibtex version 2 we need this
bibtex_bibfiles = [ "biblio.bib" ]

# Change this to "info" or "warning" to get notifications about
# undocumented Squirrel
# objects (objects with no contents).
report_undocumented_squirrel_objects = "warning"

# The encoding of source files.
source_encoding = 'utf-8-sig'

# TODO pass it to True/False for debugging/publishing
todo_include_todos = False

# The name of the Pygments (syntax highlighting) style to use.
# pygments_style = 'sphinx'
highlight_language = 'rst'
# suppress_warnings = ["misc.highlighting_failure","ref.cmd","ref.tacn"]
suppress_warnings = ["misc.highlighting_failure"]
