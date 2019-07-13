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
| '<'                 { LANGLE }
| '>'                 { RANGLE }
| ','                 { COMMA }
| ':'                 { COLON }
| ';'                 { SEMICOLON }
| "="                 { EQ }
| '('                 { LPAREN }
| ')'                 { RPAREN }
| '|'                 { PARALLEL }
| "->"                { ARROW }
| ":="                { ASSIGN }
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
| "as"                { AS }
| "null"              { NULL }
| name as n           { ID (n) }
| eof                 { EOF }
