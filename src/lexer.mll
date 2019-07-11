{
  open Lexing
  open Parser
}

let name = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let int = ['0'-'9'] ['0'-'9']*

rule token = parse
| [' ' '\t' '\n']     { token lexbuf }
| '#' [^'\n']* '\n'   { token lexbuf }
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
