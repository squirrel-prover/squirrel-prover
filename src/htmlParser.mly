%{
  module L  = Location
  module T  = Tactics
%}

%token <char> CHAR 
%token <string> DOT
%token <string> COM

%start main
%type <string * (string list)> main

%%

main:
| CHAR main   { let (line, coms) = $2 in
                ((String.make 1 $1) ^ line, coms) }
| COM main    { let (line, coms) = $2 in
                (line, $1 :: coms) }
| DOT         { ($1, []) }
