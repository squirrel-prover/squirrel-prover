import sys
import os

sys.path.append(os.path.abspath("./_ext"))

# Configuration file for the Sphinx documentation builder.
#
# For the full list of built-in configuration values, see the documentation:
# https://www.sphinx-doc.org/en/master/usage/configuration.html

# -- Project information -----------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#project-information

project = 'Squirrel'
copyright = '2023, Squirrel developpers'
author = 'Squirrel developpers'
release = '0.1'

# -- General configuration ---------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#general-configuration

extensions = [
    'sphinx_tabs.tabs', # Needs `pip install sphinx-tabs`
    'myst_parser', # Needs `pip install myst-parser`
    'sphinxcontrib.bibtex',
    'helloworld',
    'squirreldomain'
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
exclude_patterns = []

# -- Options for HTML output -------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#options-for-html-output

# html_theme = 'alabaster'
html_theme = 'sphinx_rtd_theme'
# Needs `pip install sphinx_rtd_theme beautifulsoup4 \
# antlr4-python3-runtime==4.7.1 pexpect sphinxcontrib-bibtex`

# Add any paths that contain custom themes here, relative to this directory.
import sphinx_rtd_theme
html_theme_path = [sphinx_rtd_theme.get_html_theme_path()]

html_static_path = ['_static']

html_context = {
    'display_github': True,
    'github_user': 'squirrel-prover',
    'github_repo': 'squirrel-prover',
    'github_version': 'master',
    'conf_py_path': '/documentation/sphinx/'
}
# since sphinxcontrib-bibtex version 2 we need this
bibtex_bibfiles = [ "biblio.bib" ]

# The name of the Pygments (syntax highlighting) style to use.
# pygments_style = 'sphinx'
highlight_language = 'rst'
suppress_warnings = ["misc.highlighting_failure"]

