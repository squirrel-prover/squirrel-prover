=============
Introduction
=============

Lexical conventions
====================

Throughout the documentation we use the following lexical units:

.. prodn::
  natural ::= {+ 0 .. 9 }
  identifier ::= {| a .. z | A .. Z } {* {| a .. z | A .. Z | 0 .. 9 | ' } }

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
