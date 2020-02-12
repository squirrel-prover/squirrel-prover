{
  open Lexing
  open Parser
  let newline lexbuf =
    let p = lexbuf.Lexing.lex_curr_p in
    let q =
      { p with Lexing.
        pos_lnum = p.Lexing.pos_lnum+1 ;
        pos_bol = p.Lexing.pos_cnum }
    in
      lexbuf.Lexing.lex_curr_p <- q

  exception LexicalError of string

  let unterminated_comment () =
    raise (LexicalError "unterminated comment")


}

let name = ['a'-'z' 'A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']*
let int = ['0'-'9'] ['0'-'9']*

rule token = parse
| [' ' '\t']              { token lexbuf }
| '\n'                    { newline lexbuf ; token lexbuf }
| "(*" { comment lexbuf; token lexbuf }
| "!_" (['a'-'z']* as i)  { BANG i }
| "&&"                { AND }
| "||"                { OR }
| "not"               { NOT }
| "True"              { TRUE }
| "False"             { FALSE }
| '<'                 { LANGLE }
| '>'                 { RANGLE }
| ','                 { COMMA }
| '.'                 { DOT }
| ':'                 { COLON }
| ';'                 { SEMICOLON }
| "="                 { EQ }
| "<>"                { NEQ }
| ">="                { GEQ }
| "<="                { LEQ }
| '('                 { LPAREN }
| ')'                 { RPAREN }
| '|'                 { PARALLEL }
| "->"                { ARROW }
| "=>"                { DARROW }
| ":="                { ASSIGN }
| "-"                 { MINUS }
| "@"                 { AT }
| "happens"           { HAPPENS }
| "if"                { IF }
| "then"              { THEN }
| "else"              { ELSE }
| "let"               { LET }
| "XOR"               { XOR }
| "in"                { IN }
| "out"               { OUT }
| "new"               { NEW }
| "try find"          { FIND }
| "such that"         { SUCHTHAT }
| "term"              { TERM }
| "process"           { PROCESS }
| "abstract"          { ABSTRACT }
| "name"              { NAME }
| "mutable"           { MUTABLE }
| "system"            { SYSTEM }
| "hash"              { HASH }
| "aenc"              { AENC }
| "init"              { INIT }
| "index"             { INDEX }
| "message"           { MESSAGE }
| "channel"           { CHANNEL }
| "boolean"           { BOOLEAN }
| "timestamp"         { TIMESTAMP }
| "null"              { NULL }
| "pred"              { PRED }
| "diff"              { DIFF }
| "left"              { LEFT }
| "right"             { RIGHT }
| "forall"            { FORALL }
| "exists"            { EXISTS }
| "goal"              { GOAL }
| "equiv"             { EQUIV }
| "axiom"             { AXIOM }
| "Proof."            { PROOF }
| "Qed."              { QED }
| "apply"             { APPLY }
| "help"              { HELP }
| "to"                { TO }
| "cycle"             { CYCLE }
| "undo"              { UNDO }
| "try"               { TRY }
| "repeat"            { REPEAT }
| "nosimpl"           { NOSIMPL }
| '+'                 { PLUS }
| name as n           { ID (n) }
| int as i            { INT (int_of_string i) }
| eof                 { EOF }

and comment = parse
  | "*)"        { () }
  | "(*"        { comment lexbuf; comment lexbuf }
  | "\n"     { new_line lexbuf; comment lexbuf }
  | eof         { unterminated_comment () }
  | _           { comment lexbuf }
