%token <string> ID
%token LPAREN RPAREN
%token LANGLE RANGLE
%token EQ COMMA SEMICOLON COLON
%token LET IN IF THEN ELSE FIND SUCHTHAT
%token NEW OUT PARALLEL AS
%token CHANNEL TERM PROCESS HASH AENC NAME MUTABLE SYSTEM
%token INDEX MESSAGE BOOLEAN ARROW
%token EOF

%left PARALLEL
%right ELSE

%start theory
%type <unit> theory
%type <Theory.fact> fact

%%

(* Terms *)

term:
| ID term_list                   { Theory.make_term $1 $2 }
| LANGLE term COMMA term RANGLE  { Theory.make_pair $2 $4 }
| LPAREN term RPAREN             { $2 }

term_list:
|                                { [] }
| LPAREN term in_tm_list RPAREN  { $2::$3 }

in_tm_list:
|                                { [] }
| COMMA term in_tm_list          { $2::$3 }

(* Facts, aka booleans *)

ord:
| EQ                             { Theory.Eq }

fact:
| term ord term                  { Term.Atom (Theory.Compare ($2,$1,$3)) }
| ID term_list                   { Term.Atom (Theory.make_term $1 $2) }

(* Processes *)

process:
|                                { Process.Null }
| process PARALLEL process       { Process.Parallel ($1,$3) }
| LPAREN process RPAREN          { $2 }
| ID term_list                   { Process.Apply ($1,$2,$1) }
| ID term_list AS ID             { Process.Apply ($1,$2,$4) }
| NEW ID SEMICOLON process       { Process.New ($2,$4) }
| IN LPAREN ID COMMA ID RPAREN SEMICOLON process
                                 { let c = Channel.of_string $3 in
                                     Process.In (c,$5,$8) }
| OUT LPAREN ID COMMA term RPAREN SEMICOLON process
                                 { let c = Channel.of_string $3 in
                                     Process.Out (c,$5,$8) }
| IF fact THEN process else_process
                                 { Process.Exists ([],$2,$4,$5) }
| FIND indices SUCHTHAT fact IN process else_process
                                 { Process.Exists ($2,$4,$6,$7) }
| LET ID EQ term IN process      { Process.Let ($2,$4,$6) }

else_process:
|                                { Process.Null }
| ELSE process                   { $2 }

indices:
| ID                             { [$1] }
| ID COMMA indices               { $1::$3 }

kind:
| INDEX                          { Theory.Index }
| MESSAGE                        { Theory.Message }
| BOOLEAN                        { Theory.Boolean }

arg_list:
|                                { [] }
| ID COLON kind                  { [$1,$3] }
| ID COLON kind COMMA arg_list   { ($1,$3)::$5 }

name_type:
| MESSAGE                        { 0 }
| INDEX ARROW name_type          { 1+$3 }

msg_or_bool:
| MESSAGE                        { Theory.Message }
| BOOLEAN                        { Theory.Boolean }

state_type:
| msg_or_bool                    { 0, $1 }
| INDEX ARROW state_type         { let n,k = $3 in n+1,k }

declaration:
| HASH ID                        { Theory.declare_hash $2 }
| AENC ID                        { Theory.declare_aenc $2 }
| NAME ID COLON name_type        { Theory.declare_name $2 $4 }
| MUTABLE ID COLON state_type    { Theory.declare_state $2 (fst $4) (snd $4) }
| CHANNEL ID                     { Channel.declare $2 }
| TERM ID arg_list COLON msg_or_bool EQ term
                                 { Theory.declare_macro $2 $3 $5 $7 }
| PROCESS ID arg_list EQ process { Process.declare $2 $3 $5 }

theory:
| declaration theory             { () }
| SYSTEM process EOF             { Process.declare_system $2 }
