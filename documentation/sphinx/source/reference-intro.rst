=========
Notations
=========

Thourghout this documention, we rely on the classical `EBNF notations <https://en.wikipedia.org/wiki/Extended_Backus%E2%80%93Naur_form>`_ for presenting Squirrel's syntax, with the following conventions.

Lexical conventions
====================

Throughout the documentation we use the following lexical units:

.. prodn::
  natural ::= {+ 0 .. 9 }
  ident ::= {| a .. z | A .. Z } {* {| a .. z | A .. Z | 0 .. 9 | ' } }

Infix operators
~~~~~~~~~~~~~~~

Squirrel supports the following syntax for infix operators

.. prodn::
   infix_op ::= &&
            | %|%|
            | xor
            | =>
            | <=>
            | @left_infix_op
            | @right_infix_op

.. prodn::
   left_infix_op ::= ^  { {* @infix_char} | {* 0 .. 9 } {+ @infix_char} }
   right_infix_op ::= {| + | - | * | %| | & | ~ } { {* @infix_char} | {* 0 .. 9 } {+ @infix_char} }
   infix_char ::= {| ^ | + | - | * | %| | & | ~ | < | > }
