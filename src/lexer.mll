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
}

let name = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let int = ['0'-'9'] ['0'-'9']*

rule token = parse
| [' ' '\t']              { token lexbuf }
| '\n'                    { newline lexbuf ; token lexbuf }
| '#' [^'\n']* '\n'       { newline lexbuf ; token lexbuf }
| "!_" (['a'-'z']* as i)  { BANG i }
| "and"               { AND }
| "or"                { OR }
| "not"               { NOT }
| "true"              { TRUE }
| "false"             { FALSE }
| '<'                 { LANGLE }
| '>'                 { RANGLE }
| ','                 { COMMA }
| '.'                 { DOT }
| ':'                 { COLON }
| ';'                 { SEMICOLON }
| "="                 { EQ }
| "<>"                { NEQ }
| ">="                { GEQ }
| ">"                 { GT }
| "<="                { LEQ }
| "<"                 { LT }
| '('                 { LPAREN }
| ')'                 { RPAREN }
| '['                 { LBRACKET }
| ']'                 { RBRACKET }
| '|'                 { PARALLEL }
| '/'                 { SLASH }
| "->"                { ARROW }
| "=>"                { DARROW }
| ":="                { ASSIGN }
| "@"                 { AT }
| "if"                { IF }
| "then"              { THEN }
| "else"              { ELSE }
| "let"               { LET }
| "in"                { IN }
| "out"               { OUT }
| "new"               { NEW }
| "try find"          { FIND }
| "such that"         { SUCHTHAT }
| "term"              { TERM }
| "process"           { PROCESS }
| "name"              { NAME }
| "mutable"           { MUTABLE }
| "system"            { SYSTEM }
| "hash"              { HASH }
| "aenc"              { AENC }
| "index"             { INDEX }
| "message"           { MESSAGE }
| "channel"           { CHANNEL }
| "boolean"           { BOOLEAN }
| "timestamp"         { TIMESTAMP }
| "as"                { AS }
| "null"              { NULL }
| "forall"            { FORALL }
| "exists"            { EXISTS }
| "goal"              { GOAL }
| name as n           { ID (n) }
| int as i            { INT (int_of_string i) }
| eof                 { EOF }
