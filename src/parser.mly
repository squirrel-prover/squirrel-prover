%token <int> INT
%token <string> ID
%token <string> BANG
%token AT
%token LPAREN RPAREN
%token LANGLE RANGLE
%token AND OR NOT TRUE FALSE
%token EQ NEQ GEQ LEQ COMMA SEMICOLON COLON PLUS MINUS UNDERSCORE
%token LET IN IF THEN ELSE FIND SUCHTHAT
%token NEW OUT PARALLEL AS NULL
%token CHANNEL TERM PROCESS HASH AENC NAME ABSTRACT MUTABLE SYSTEM
%token INDEX MESSAGE BOOLEAN TIMESTAMP ARROW ASSIGN
%token EXISTS FORALL GOAL DARROW AXIOM
%token LBRACKET RBRACKET DOT SLASH
%token ADMIT SPLIT LEFT RIGHT INTRO FORALLINTRO ANYINTRO EXISTSINTRO CONGRUENCE APPLY TO
%token NOTRACES EQNAMES EQTIMESTAMPS EUF TRY CYCLE IDENT ORELSE REPEAT COLLISION
%token PROOF QED UNDO
%token EOF

%token EMPTY_ELSE

%nonassoc EMPTY_ELSE
%nonassoc ELSE
%left ARROW
%left OR
%left AND
%nonassoc NOT

%left ORELSE
%left PLUS
%nonassoc REPEAT
%left SEMICOLON

%start theory
%start top_process
%start interactive
%type <unit> theory
%type <Process.process> top_process
%type <Prover.parsed_input> interactive

%%

(* Actions *)

i_list:
|                                 { [] }
| COMMA; ind=ID; l=i_list         { ind :: l }

index_list:
|                                 { [] }
| LBRACKET RBRACKET               { [] }
| LBRACKET; ind=ID; l=i_list; RBRACKET
                                  { ind :: l }
saction:
| par=INT; lpar=index_list        { (par,lpar,0,[]) }
| par=INT; lpar=index_list; SLASH; sum=INT; lsum=index_list
                                  { (par,lpar,sum,lsum) }

action:
| act=saction;                       { [act] }
| act=saction; UNDERSCORE; l=action  { act :: l }

(* Terms *)

term:
| aterm                          { $1 }
| LPAREN term RPAREN             { $2 }

aterm:
| a=action                       { Theory.Taction (Theory.make_action a) }
| ID term_list                   { Theory.make_term $1 $2 }
| ID term_list AT term           { let ts = $4 in
		                   Theory.make_term ~at_ts:(Some ts) $1 $2 }
| LANGLE term COMMA term RANGLE  { Theory.make_pair $2 $4 }

term_list:
|                                { [] }
| LPAREN RPAREN                  { [] }
| LPAREN term tm_list RPAREN     { $2::$3 }

tm_list:
|                                { [] }
| COMMA term tm_list             { $2::$3 }

(* Facts, aka booleans *)

ord:
| EQ                             { Term.Eq }
| NEQ                            { Term.Neq }
| LEQ                            { Term.Leq }
| LANGLE                         { Term.Lt }
| GEQ                            { Term.Geq }
| RANGLE                         { Term.Gt }

fact:
| LPAREN fact RPAREN             { $2 }
| fact AND fact                  { Term.And  ($1,$3) }
| fact OR fact                   { Term.Or  ($1,$3) }
| fact ARROW fact                { Term.Impl  ($1,$3) }
| NOT fact                       { Term.Not  ($2) }
| FALSE                          { Term.False }
| TRUE                           { Term.True }
| aterm ord aterm                { Term.Atom (Theory.Compare ($2,$1,$3)) }
| ID term_list                   { Term.Atom (Theory.make_term $1 $2) }

(* Processes *)

process:
| NULL                           { Process.Null }
| LPAREN processes RPAREN        { $2 }
| ID term_list                   { Process.Apply ($1,$2,$1) }
| ID term_list AS ID             { Process.Apply ($1,$2,$4) }
| NEW ID SEMICOLON process       { Process.New ($2,$4) }
| IN LPAREN channel COMMA ID RPAREN process_cont
                                 { Process.In ($3,$5,$7) }
| OUT LPAREN channel COMMA term RPAREN process_cont
                                 { Process.Out ($3,$5,$7) }
| IF fact THEN process else_process
                                 { Process.Exists ([],$2,$4,$5) }
| FIND indices SUCHTHAT fact IN process else_process
                                 { Process.Exists ($2,$4,$6,$7) }
| LET ID EQ term IN process      { Process.Let ($2,$4,$6) }
| ID term_list ASSIGN term process_cont
                                 { let to_idx = function
                                     | Theory.Var x -> x
                                     | _ -> failwith "index variable expected"
                                   in
                                   let l = List.map to_idx $2 in
                                   Process.Set ($1,l,$4,$5) }
| BANG process                   { Process.Repl ($1,$2) }

processes:
| process                        { $1 }
| process PARALLEL processes     { Process.Parallel ($1,$3) }

process_cont:
|                                { Process.Null }
| SEMICOLON process              { $2 }

else_process:
| %prec EMPTY_ELSE               { Process.Null }
| ELSE process                   { $2 }

channel:
| ID                             { try Channel.of_string $1 with Not_found ->
                                     failwith "unknown channel" }

indices:
| ID                             { [$1] }
| ID COMMA indices               { $1::$3 }

kind:
| INDEX                          { Theory.Index }
| MESSAGE                        { Theory.Message }
| BOOLEAN                        { Theory.Boolean }
| TIMESTAMP                      { Theory.Timestamp }

arg_list:
|                                { [] }
| ID COLON kind                  { [$1,$3] }
| ID COLON kind COMMA arg_list   { ($1,$3)::$5 }


opt_arg_list:
| LPAREN arg_list RPAREN         { $2 }
|                                { [] }


name_type:
| MESSAGE                        { 0 }
| INDEX ARROW name_type          { 1+$3 }

msg_or_bool:
| MESSAGE                        { Theory.Message }
| BOOLEAN                        { Theory.Boolean }

state_type:
| msg_or_bool                    { 0, $1 }
| INDEX ARROW state_type         { let n,k = $3 in n+1,k }

abs_type:
| msg_or_bool                    { [],$1 }
| msg_or_bool ARROW abs_type     { let l,r = $3 in $1::l,r }

declaration:
| HASH ID                        { Theory.declare_hash $2 }
| AENC ID                        { Theory.declare_aenc $2 }
| NAME ID COLON name_type        { Theory.declare_name $2 $4 }
| ABSTRACT ID COLON abs_type     { let l,r = $4 in
                                     Theory.declare_abstract $2 l r }
| MUTABLE ID COLON state_type    { Theory.declare_state $2 (fst $4) (snd $4) }
| CHANNEL ID                     { Channel.declare $2 }
| TERM ID opt_arg_list COLON msg_or_bool EQ term
                                 { Theory.declare_macro $2 $3 $5 $7 }
| PROCESS ID opt_arg_list EQ process
                                 { Process.declare $2 $3 $5 }
| AXIOM f=formula		 { Prover.add_proved_goal
                                     ("unnamed_goal", Prover.make_goal f) }
| AXIOM i=ID COLON f=formula     { Prover.add_proved_goal
                                     (i, Prover.make_goal f) }

q_vars:
| LPAREN arg_list RPAREN                       { ($2, Term.True) }
| LPAREN arg_list RPAREN SUCHTHAT fact         { ($2, $5) }

formula:
| fact                           { ( ([],Term.True),
				     ([],Term.True),
				     Term.True, $1 ) }
| EXISTS q_vars COLON fact       { ( ([],Term.True),
                   	             $2,
				     Term.True, $4 ) }
| FORALL q_vars COLON fact       { ( $2,
				     ([],Term.True),
				     Term.True, $4 ) }
| FORALL q_vars COLON fact DARROW EXISTS q_vars COLON fact
                                 { ($2, $7, $4, $9) }

tactic_params:
|                               { [] }
| t=term                        { [t] }
| t=term COMMA ts=tactic_params { t::ts }

tac:
  | LPAREN t=tac RPAREN               { t }
  | ADMIT                             { Prover.Admit }
  | IDENT                             { Prover.Ident }
  | FORALLINTRO                       { Prover.ForallIntro }
  | EXISTSINTRO t=tactic_params       { Prover.ExistsIntro (Prover.parse_args_exists t)}
  | ANYINTRO                          { Prover.AnyIntro }
  | INTRO                             { Prover.Intro }
  | LEFT                              { Prover.Left }
  | RIGHT                             { Prover.Right }
  | SPLIT                             { Prover.Split }
  | CONGRUENCE                        { Prover.GammaAbsurd }
  | NOTRACES                          { Prover.ConstrAbsurd }
  | EQNAMES                           { Prover.EqNames }
  | EQTIMESTAMPS                      { Prover.EqTimestamps }
  | COLLISION                         { Prover.CollisionResistance }
  | EUF i=INT                         { Prover.Euf i }
  | CYCLE i=INT                       { Prover.Cycle i }
  | CYCLE MINUS i=INT                 { Prover.Cycle (-i) }
  /* | LBRACKET t=tac RBRACKET        { Prover.ProveAll t } */
  | l=tac SEMICOLON r=tac             { Prover.AndThen (l,r) }
  | l=tac PLUS r=tac                  { Prover.OrElse (l, r) }
  | TRY l=tac ORELSE r=tac            { Prover.Try (l, r) }
  | APPLY i=ID                        { Prover.Apply (i, Prover.parse_args i []) }
  | APPLY i=ID TO t=tactic_params     { Prover.Apply (i, Prover.parse_args i t) }
  | REPEAT t=tac                      { Prover.Repeat (t) }


qed:
| QED                                 { () }

undo:
| UNDO i=INT DOT                      { i }

tactic:
| t=tac DOT                           { t }

goal:
| GOAL i=ID COLON f=formula DOT   { Prover.Gm_goal (i, Prover.make_goal f) }
| GOAL f=formula DOT              { Prover.Gm_goal ("unnamed_goal",
                                                      Prover.make_goal f) }
| PROOF                           { Prover.Gm_proof }

theory:
| declaration theory             { () }
| SYSTEM process DOT             { Process.declare_system $2 }

top_process:
| process EOF                    { $1 }

interactive :
| theory                          { Prover.ParsedInputDescr }
| undo                            { Prover.ParsedUndo $1 }
| tactic                          { Prover.ParsedTactic $1 }
| qed                             { Prover.ParsedQed }
| goal                            { Prover.ParsedGoal $1 }
| EOF                             { Prover.EOF }
