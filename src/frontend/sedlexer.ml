open Sedlexing
open Parser

exception Lexical_error of string

let unterminated_comment () = raise (Lexical_error "unterminated comment")
let alpha = [%sedlex.regexp? 'a' .. 'z' | 'A' .. 'Z']
let digit = [%sedlex.regexp? '0' .. '9']
let alphanum = [%sedlex.regexp? alpha | digit]
let whitespace = [%sedlex.regexp? zs]
let name = [%sedlex.regexp? alpha, Star (alphanum | '_' | '\'')]

let path =
  [%sedlex.regexp? '.', '/', Plus (alphanum | '_' | '.' | '-' | '/'), ".sp"]

let int = [%sedlex.regexp? Plus digit]
let drop_n_first_chars ~n s = String.sub s n (String.length s - 2)

(* Hard-coded in Symbols.ml ! Do not change. *)
let right_infix_char_first = [%sedlex.regexp? '+' | '-' | '*' | '|' | '&' | '~']
let left_infix_char_first = [%sedlex.regexp? '^']

let infix_char =
  [%sedlex.regexp? right_infix_char_first | left_infix_char_first | '<' | '>']

let left_infix_symb =
  [%sedlex.regexp?
    left_infix_char_first, (Star infix_char | Star '0' .. '9', Plus infix_char)]

let right_infix_symb =
  [%sedlex.regexp?
    right_infix_char_first, (Star infix_char | Star '0' .. '9', Plus infix_char)]

let rec token buf =
  match%sedlex buf with
  | whitespace | '\t' -> token buf
  | '\n' ->
      new_line buf;
      token buf
  | "(*" ->
      comment buf;
      token buf
  | "True" -> TRUE
  | "!_", name -> BANG (Utf8.lexeme buf |> drop_n_first_chars ~n:2)
  | "&&" -> AND
  | "/\\" -> GAND
  | "\\/" -> GOR
  | "||" -> OR
  | "not" -> NOT
  | "True" -> TRUE
  | "False" -> FALSE
  | '"' -> QUOTE
  | '<' -> LANGLE
  | '>' -> RANGLE
  | '[' -> LBRACKET
  | ']' -> RBRACKET
  | '{' -> LBRACE
  | '}' -> RBRACE
  | '?' -> QMARK
  | ',' -> COMMA
  | "!" -> BANGU
  | '.' -> DOT
  | '#' -> SHARP
  | '$' -> DOLLAR
  | ':' -> COLON
  | ":=" -> COLONEQ
  | ';' -> SEMICOLON
  | '*' -> STAR
  | '_' -> UNDERSCORE
  | "//" -> SLASHSLASH
  | "/=" -> SLASHEQUAL
  | "//=" -> SLASHSLASHEQUAL
  | '/' -> SLASH
  | "@/" -> ATSLASH
  | "=" -> EQ
  | "<>" -> NEQ
  | ">=" -> GEQ
  | "<=" -> LEQ
  | '(' -> LPAREN
  | ')' -> RPAREN
  | '|' -> PARALLEL
  | "->" -> ARROW
  | "<-" -> RARROW
  | "=>" -> DARROW
  | "<=>" -> DEQUIVARROW
  | "-" -> MINUS
  | "@" -> AT
  | '~' -> TILDE
  | '+' -> PLUS
  | '\'' -> TICK
  | '%' -> PERCENT
  | int -> INT (Utf8.lexeme buf |> int_of_string)
  | "if" -> IF
  | "then" -> THEN
  | "else" -> ELSE
  | "let" -> LET
  | "XOR" -> XOR
  | "by" -> BY
  | "in" -> IN
  | "out" -> OUT
  | "new" -> NEW
  | "try find" -> FIND
  | "such that" -> SUCHTHAT
  | "process" -> PROCESS
  | "abstract" -> ABSTRACT
  | "action" -> ACTION
  | "op" -> OP
  | "predicate" -> PREDICATE
  | "fun" -> FUN
  | "type" -> TYPE
  | "name" -> NAME
  | "mutable" -> MUTABLE
  | "system" -> SYSTEM
  | "set" -> SET
  | "hash" -> HASH
  | "aenc" -> AENC
  | "senc" -> SENC
  | "signature" -> SIGNATURE
  | "intro" -> INTRO
  | "destruct" -> DESTRUCT
  | "fa" -> FA
  | "cs" -> CS
  | "as" -> AS
  | "index" -> INDEX
  | "message" -> MESSAGE
  | "channel" -> CHANNEL
  | "boolean" -> BOOLEAN
  | "bool" -> BOOL
  | "timestamp" -> TIMESTAMP
  | "null" -> NULL
  | "seq" -> SEQ
  | "oracle" -> ORACLE
  | "with" -> WITH
  | "where" -> WHERE
  | "time" -> TIME
  | "diff" -> DIFF
  | "forall" -> FORALL
  | "exists" -> EXISTS
  | "Forall" -> UFORALL
  | "Exists" -> UEXISTS
  | "splitseq" -> SPLITSEQ
  | "constseq" -> CONSTSEQ
  | "memseq" -> MEMSEQ
  | "remember" -> REMEMBER
  | "dependent" -> DEPENDENT
  | "lemma" -> LEMMA
  | "theorem" -> THEOREM
  | "local" -> LOCAL
  | "global" -> GLOBAL
  | "equiv" -> EQUIV
  | "axiom" -> AXIOM
  | "Proof." -> PROOF
  | "hint" -> HINT
  | "Qed." -> QED
  | "Reset." -> RESET
  | "Abort." -> ABORT
  | "help" -> HELP
  | "cycle" -> CYCLE
  | "undo" -> UNDO
  | "try" -> TRY
  | "repeat" -> REPEAT
  | "assert" -> ASSERT
  | "localize" -> LOCALIZE
  | "have" -> HAVE
  | "reduce" -> REDUCE
  | "auto" -> AUTO
  | "simpl" -> SIMPL
  | "exn" -> EXN
  | "use" -> USE
  | "rewrite" -> REWRITE
  | "trans" -> TRANS
  | "fresh" -> FRESH
  | "apply" -> APPLY
  | "revert" -> REVERT
  | "generalize" -> GENERALIZE
  | "induction" -> INDUCTION
  | "depends" -> DEPENDS
  | "clear" -> CLEAR
  | "ddh" -> DDH
  | "cdh" -> CDH
  | "gdh" -> GDH
  | "nosimpl" -> NOSIMPL
  | "rename" -> RENAME
  | "gprf" -> GPRF
  | "gcca" -> GCCA
  | "checkfail" -> CHECKFAIL
  | "include" -> INCLUDE
  | "smt" -> SMT
  | "print" -> PRINT
  | "search" -> SEARCH
  | path -> PATH (Utf8.lexeme buf)
  | name -> ID (Utf8.lexeme buf)
  | eof -> EOF
  | left_infix_symb -> LEFTINFIXSYMB (Utf8.lexeme buf)
  | right_infix_symb -> RIGHTINFIXSYMB (Utf8.lexeme buf)
  | _ -> failwith "Unexpected character"

and comment buf =
  match%sedlex buf with
  | "*)" -> ()
  | "(*" ->
      comment buf;
      comment buf
  | "\n" ->
      new_line buf;
      comment buf
  | eof -> unterminated_comment ()
  | any -> comment buf
  | _ -> failwith "Unexpected character"
