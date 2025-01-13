open Sedlexing
open Parser

exception Lexical_error of string

let unterminated_comment () = raise (Lexical_error "unterminated comment")
let alpha = [%sedlex.regexp? 'a' .. 'z' | 'A' .. 'Z']
let digit = [%sedlex.regexp? '0' .. '9']
let alphanum = [%sedlex.regexp? alpha | digit]
let whitespace = [%sedlex.regexp? zs | '\t']

let emoji =
  [%sedlex.regexp?
    ( 0x00A9 | 0x00AE | 0x203C | 0x2049 | 0x20E3 | 0x2122 | 0x2139
    | 0x2194 .. 0x2199
    | 0x21A9 .. 0x21AA
    | 0x231A | 0x231B | 0x2328 | 0x23CF
    | 0x23E9 .. 0x23F3
    | 0x23F8 .. 0x23FA
    | 0x24C2 | 0x25AA | 0x25AB | 0x25B6 | 0x25C0
    | 0x25FB .. 0x25FE
    | 0x2600 .. 0x27EF
    | 0x2934 | 0x2935
    | 0x2B00 .. 0x2BFF
    | 0x3030 | 0x303D | 0x3297 | 0x3299
    | 0x1F000 .. 0x1F02F
    | 0x1F0A0 .. 0x1F0FF
    | 0x1F100 .. 0x1F64F
    | 0x1F680 .. 0x1F6FF
    | 0x1F910 .. 0x1F96B
    | 0x1F980 .. 0x1F9E0 )]

(* identifier starting by a lower-case character *)
let lid =
  [%sedlex.regexp? (ll | emoji), Star (ll | lu | emoji | digit | '_' | '\'')]

(* identifier starting by an upper-case character *)
let uid =
  [%sedlex.regexp? (lu), Star (ll | lu | emoji | digit | '_' | '\'')]

let quoted_string =
  [%sedlex.regexp? '"', Plus (alphanum | '_' | '.' | '-' | '/'), '"']

let int = [%sedlex.regexp? Plus digit]
let drop_n_first_chars ~n s = String.sub s n (String.length s - 2)

(*------------------------------------------------------------------*)
(* Must be synchronized with the corresponding code in [Symbols.ml]! *)

(* `<`,`>` and `=` are manually added after-ward. *)
let right_infix_char_first = 
  [%sedlex.regexp? '+' | '-' | '*' | '|' | '&' | '~' | Sub (math, ('<' | '>' | '='))]
let left_infix_char_first = [%sedlex.regexp? '^']

let infix_char =
  [%sedlex.regexp? right_infix_char_first | left_infix_char_first | math]

let left_infix_symb =
  [%sedlex.regexp?
    left_infix_char_first, Star (infix_char | Star '0' .. '9', Plus infix_char)]

let right_infix_symb =
  [%sedlex.regexp?
    right_infix_char_first, Star (infix_char | Star '0' .. '9', Plus infix_char)]

(*------------------------------------------------------------------*)

let rec token buf =
  let (!?) token =
    if Feedback.keywords_as_ids () then
      let str = Utf8.lexeme buf in
      if Char.lowercase_ascii str.[0] = str.[0] then LID str else UID str
    else
      token
  in
  match%sedlex buf with
  | whitespace -> token buf
  | '\n' -> token buf
  | "(*" ->
      comment buf;
      token buf
  | "!_", (lid | uid) -> BANG (Utf8.lexeme buf |> drop_n_first_chars ~n:2)
  | "&&" -> AND
  | "/\\" -> GAND
  | "\\/" -> GOR
  | "||" -> OR
  | '<' -> LANGLE
  | '>' -> RANGLE
  | "<:" -> LANGLECOLON
  | '[' -> LBRACKET
  | ']' -> RBRACKET
  | '{' -> LBRACE
  | '}' -> RBRACE
  | '?' -> QMARK
  | ',' -> COMMA
  | "!" -> BANGU
  | "#init" -> SHARPINIT
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
  | "|\""-> LQUOTED
  | "\"|"-> RQUOTED
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
  | '`' -> BACKTICK
  | '%' -> PERCENT
  | int -> INT (Utf8.lexeme buf |> int_of_string)

  | "Proof." -> PROOF
  | "Qed." -> QED
  | "Abort." -> ABORT
  | "Reset." -> RESET

  | "abstract" -> !?ABSTRACT
  | "action" -> !?ACTION
  | "aenc" -> !?AENC
  | "apply" -> !?APPLY
  | "as" -> !?AS
  | "assert" -> !?ASSERT
  | "auto" -> !?AUTO
  | "axiom" -> !?AXIOM
  | "bool" -> !?BOOL
  | "boolean" -> !?BOOLEAN
  | "by" -> !?BY
  | "case" -> !?CASE
  | "cdh" -> !?CDH
  | "channel" -> !?CHANNEL
  | "checkfail" -> !?CHECKFAIL
  | "clear" -> !?CLEAR
  | "constseq" -> !?CONSTSEQ
  | "crypto" -> !?CRYPTO
  | "cs" -> !?CS
  | "cycle" -> !?CYCLE
  | "ddh" -> !?DDH
  | "dependent" -> !?DEPENDENT
  | "depends" -> !?DEPENDS
  | "destruct" -> !?DESTRUCT
  | "deduce" -> !?DEDUCE
  | "diff" -> !?DIFF
  | "else" -> !?ELSE
  | "equiv" -> !?EQUIV
  | "exists" -> !?EXISTS
  | "Exists" -> !?UEXISTS
  | "end" -> !?END
  | "exn" -> !?EXN               
  | "fa" -> !?FA
  | "False" -> !?FALSE
  | "forall" -> !?FORALL
  | "Forall" -> !?UFORALL
  | "fresh" -> !?FRESH
  | "fun" -> !?FUN
  | "game" -> !?GAME
  | "gcca" -> !?GCCA
  | "gdh" -> !?GDH
  | "generalize" -> !?GENERALIZE
  | "global" -> !?GLOBAL
  | "gprf" -> !?GPRF
  | "hash" -> !?HASH
  | "have" -> !?HAVE
  | "ghave" -> !?GHAVE
  | "help" -> !?HELP
  | "hint" -> !?HINT
  | "if" -> !?IF
  | "include" -> !?INCLUDE
  | "index" -> !?INDEX
  | "induction" -> !?INDUCTION
  | "in" -> !?IN
  | "intro" -> !?INTRO
  | "lemma" -> !?LEMMA
  | "let" -> !?LET
  | "Let" -> !?LLET
  | "localize" -> !?LOCALIZE
  | "local" -> !?LOCAL
  | "memseq" -> !?MEMSEQ
  | "message" -> !?MESSAGE
  | "mutable" -> !?MUTABLE
  | "name" -> !?NAME
  | "namespace" -> !?NAMESPACE
  | "new" -> !?NEW
  | "nosimpl" -> !?NOSIMPL
  | "not" -> !?NOT
  | "null" -> !?NULL
  | "op" -> !?OP
  | "open" -> !?OPEN
  | "close" -> !?CLOSE
  | "oracle" -> !?ORACLE
  | "out" -> !?OUT
  | "predicate" -> !?PREDICATE
  | "print" -> !?PRINT
  | "process" -> !?PROCESS
  | "prof" -> !?PROF
  | "reduce" -> !?REDUCE
  | "remember" -> !?REMEMBER
  | "rename" -> !?RENAME
  | "repeat" -> !?REPEAT
  | "return" -> !?RETURN
  | "revert" -> !?REVERT
  | "rewrite" -> !?REWRITE
  | "rnd" -> !?RND
  | "search" -> !?SEARCH
  | "senc" -> !?SENC
  | "seq" -> !?SEQ
  | "set" -> !?SET
  | "signature" -> !?SIGNATURE
  | "simpl" -> !?SIMPL
  | "smt" -> !?SMT
  | "deduce" -> !?DEDUCE
  | "splitseq" -> !?SPLITSEQ
  | "such that" -> !?SUCHTHAT
  | "system" -> !?SYSTEM
  | "tactic" -> !?TACTIC
  | "then" -> !?THEN
  | "theorem" -> !?THEOREM
  | "timestamp" -> !?TIMESTAMP
  | "time" -> !?TIME
  | "trans" -> !?TRANS
  | "True" -> !?TRUE
  | "try find" -> !?FIND
  | "try" -> !?TRY
  | "type" -> !?TYPE
  | "undo" -> !?UNDO
  | "use" -> !?USE
  | "var" -> !?VAR
  | "weak" -> !?WEAK
  | "where" -> !?WHERE
  | "with" -> !?WITH
  | "XOR" -> !?XOR

  (* terminal symbol, delimiting a sentence to be parsed. *)
  | '.', (whitespace | '\n' | eof) -> TERMINAL
  | '.' -> DOT

  | quoted_string ->
    let s = Utf8.lexeme buf in
    QUOTED_STRING (String.sub s 1 (String.length s - 2))
    (* remove the enclosing quotes '"' *)

  | uid -> UID (Utf8.lexeme buf)
  | lid -> LID (Utf8.lexeme buf)
  | eof -> EOF
  | left_infix_symb -> LEFTINFIXSYMB (Utf8.lexeme buf)
  | right_infix_symb -> RIGHTINFIXSYMB (Utf8.lexeme buf)
  | _ -> failwith "Unexpected character"

and comment buf =
  match%sedlex buf with
  | "*)" -> ()
  | "(*" -> comment buf; comment buf
  | "\n" -> comment buf
  | eof -> unterminated_comment ()
  | any -> comment buf
  | _ -> failwith "Unexpected character"
