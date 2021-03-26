%{
  module L  = Location
  module T  = Tactics
%}

%token <int> INT
%token <string> ID   /* general purpose identifier */
%token <string> BANG
%token AT PRED
%token LPAREN RPAREN
%token LBRACKET RBRACKET
%token LANGLE RANGLE
%token AND OR NOT TRUE FALSE HAPPENS
%token EQ NEQ GEQ LEQ COMMA SEMICOLON COLON PLUS MINUS XOR STAR UNDERSCORE QMARK
%token LET IN IF THEN ELSE FIND SUCHTHAT
%token DIFF LEFT RIGHT NONE SEQ EXP
%token NEW OUT PARALLEL NULL
%token CHANNEL TERM PROCESS HASH AENC SENC SIGNATURE NAME ABSTRACT
%token MUTABLE SYSTEM SET
%token INIT INDEX MESSAGE BOOLEAN TIMESTAMP ARROW ASSIGN
%token EXISTS FORALL QUANTIF GOAL EQUIV DARROW DEQUIVARROW AXIOM
%token DOT SLASH BANGU SLASHEQUAL SLASHSLASH
%token WITH ORACLE EXN
%token TRY CYCLE REPEAT NOSIMPL HELP DDH CHECKFAIL ASSERT USE 
%token REWRITE REVERT CLEAR GENERALIZE DEPENDS
%token BY INTRO AS DESTRUCT
%token PROOF QED UNDO ABORT
%token EOF

%nonassoc QUANTIF
%right ARROW
%right DARROW
%right DEQUIVARROW
%left OR
%left AND
/* %nonassoc NOT */

%nonassoc EQ NEQ GEQ LEQ LANGLE RANGLE

%left XOR
%left EXP

%nonassoc empty_else
%nonassoc ELSE

%nonassoc AT

%nonassoc tac_prec

%left PLUS
%right SEMICOLON
%nonassoc BY
%nonassoc REPEAT
%nonassoc TRY
%nonassoc NOSIMPL

%start declarations
%start top_formula
%start top_process
%start interactive
%type <Decl.declarations> declarations
%type <Theory.formula> top_formula
%type <Process.process> top_process
%type <Prover.parsed_input> interactive

%%

(* Ls *)
%inline loc(X):
| x=X {
    { L.pl_desc = x;
      L.pl_loc  = L.make $startpos $endpos;
    }
  }

(* Lists *)
%inline empty:
| { () }

%inline slist(X, S):
| l=separated_list(S, X) { l }

%inline slist1(X, S):
| l=separated_nonempty_list(S, X) { l }


(* Terms *)
lsymb:
| id=loc(ID) { id }

/* non-ambiguous term */
sterm_i:
| LPAREN t=term_i RPAREN          { t }
| id=lsymb                        { Theory.App (id, []) }

| LPAREN t=term COMMA t0=term RPAREN
    { let loc = L.make $startpos $endpos in
      let fsymb = L.mk_loc loc "pair" in
      Theory.App (fsymb, [t;t0]) }

/* formula */

| DIFF LPAREN t=term COMMA t0=term RPAREN { Theory.Diff (t,t0) }
| SEQ LPAREN i=ids ARROW t=term RPAREN    { Theory.Seq (i,t) }

| NOT f=sterm                             { Theory.Not (f) }
| FALSE                                   { Theory.False }
| TRUE                                    { Theory.True }

| HAPPENS LPAREN ts=slist1(term,COMMA) RPAREN
                                          { Theory.Happens ts }

/* timestamp */

| PRED LPAREN ts=term RPAREN             { Theory.Tpred ts }
| INIT                                   { Theory.Tinit }

/* ambiguous term */
term_i:
| f=sterm_i                                  { f }
| id=lsymb terms=term_list1                  { Theory.App (id, terms) }
| id=lsymb AT ts=term                        { Theory.AppAt (id,[],ts) }
| id=lsymb terms=term_list1 AT ts=term       { Theory.AppAt (id,terms,ts) }

| t=term XOR t0=term
    { let loc = L.make $startpos $endpos in
      let fsymb = L.mk_loc loc "xor" in
      Theory.App (fsymb,  [t;t0]) }

| t=term EXP t0=term
    { let loc = L.make $startpos $endpos in
      let fsymb = L.mk_loc loc "exp" in
      Theory.App (fsymb,  [t;t0])}
 
| IF b=term THEN t=term t0=else_term
                                          { Theory.ITE (b,t,t0) }

| FIND is=indices SUCHTHAT b=term IN t=term t0=else_term
                                          { Theory.Find (is,b,t,t0) }


| f=term AND f0=term                { Theory.And (f,f0) }
| f=term OR f0=term                 { Theory.Or (f,f0) }
| f=term DARROW f0=term             { Theory.Impl (f,f0) }
| f=term o=ord f0=term                    { Theory.Compare (o,f,f0) }

| EXISTS LPAREN vs=arg_list RPAREN sep f=term %prec QUANTIF
                                 { Theory.Exists (vs,f)  }
| FORALL LPAREN vs=arg_list RPAREN sep f=term %prec QUANTIF
                                 { Theory.ForAll (vs,f)  }
| EXISTS id=lsymb COLON k=kind sep f=term %prec QUANTIF
                                 { Theory.Exists ([id,k],f)  }
| FORALL id=lsymb COLON k=kind sep f=term %prec QUANTIF
                                 { Theory.ForAll ([id,k],f)  }

| f=term DEQUIVARROW f0=term
    { let loc = L.make $startpos $endpos in
      Theory.And (L.mk_loc loc (Theory.Impl (f,f0)),
                  L.mk_loc loc (Theory.Impl (f0,f))) }

/* non-ambiguous term */
%inline else_term:
| %prec empty_else   { let loc = L.make $startpos $endpos in
                       let fsymb = L.mk_loc loc "zero" in
                       L.mk_loc loc (Theory.App (fsymb, [])) }
| ELSE t=term       { t }

sterm:
| t=loc(sterm_i) { t }

term:
| t=loc(term_i) { t }

term_list:
|                                    { [] }
| LPAREN RPAREN                      { [] }
| LPAREN t=term terms=tm_list RPAREN { t::terms }

term_list1:
| LPAREN t=term terms=tm_list RPAREN { t::terms }

tm_list:
|                           { [] }
| COMMA tm=term tms=tm_list { tm::tms }

(* Facts, aka booleans *)

%inline ord:
| EQ                             { `Eq }
| NEQ                            { `Neq }
| LEQ                            { `Leq }
| LANGLE                         { `Lt }
| GEQ                            { `Geq }
| RANGLE                         { `Gt }

kind:
| INDEX                          { Sorts.eindex }
| MESSAGE                        { Sorts.emessage }
| BOOLEAN                        { Sorts.eboolean }
| TIMESTAMP                      { Sorts.etimestamp }

arg_list:
|                                         { [] }
| is=ids COLON k=kind                     { List.map (fun x -> x,k) is }
| is=ids COLON k=kind COMMA args=arg_list { List.map (fun x -> x,k) is @ args }

ids:
| id=lsymb                             { [id] }
| id=lsymb COMMA ids=ids               { id::ids }

top_formula:
| f=term EOF                    { f }

sep:
|       {()}
| COMMA {()}

(* Processes *)

top_process:
| p=process EOF                    { p }

process_i:
| NULL                             { Process.Null }
| LPAREN ps=processes_i RPAREN     { ps }
| id=lsymb terms=term_list         { Process.Apply (id,terms) }
| id=lsymb COLON p=process         { Process.Alias (p,id) }
| NEW id=lsymb SEMICOLON p=process { Process.New (id,p) }
| IN LPAREN c=lsymb COMMA id=lsymb RPAREN p=process_cont
    { Process.In (c,id,p) }
| OUT LPAREN c=lsymb COMMA t=term RPAREN p=process_cont
    { Process.Out (c,t,p) }
| IF f=term THEN p=process p0=else_process
    { Process.Exists ([],f,p,p0) }
| FIND is=indices SUCHTHAT f=term IN p=process p0=else_process
    { Process.Exists (is,f,p,p0) }
| LET id=lsymb EQ t=term IN p=process
    { Process.Let (id,t,p) }
| id=lsymb terms=term_list ASSIGN t=term p=process_cont
    { let to_idx t = match L.unloc t with
        | Theory.App(x,[]) -> x
        | ti -> raise @@ Theory.Conv (L.loc t, Theory.Index_not_var ti)
      in
      let l = List.map to_idx terms in
      Process.Set (id,l,t,p) }
| s=loc(BANG) p=process { Process.Repl (s,p) }

process:
| p=loc(process_i) { p }

processes_i:
| p=process_i                             { p }
| p=process PARALLEL ps=loc(processes_i)  { Process.Parallel (p,ps) }

process_cont:
|                                { let loc = L.make $startpos $endpos in
                                   L.mk_loc loc Process.Null }
| SEMICOLON p=process            { p }

else_process:
| %prec empty_else               { let loc = L.make $startpos $endpos in
                                   L.mk_loc loc Process.Null }
| ELSE p=process                 { p }

indices:
| id=lsymb                          { [id] }
| id=lsymb COMMA ids=indices        { id::ids }

opt_arg_list:
| LPAREN args=arg_list RPAREN    { args }
|                                { [] }

name_type:
| MESSAGE                        { 0 }
| INDEX ARROW t=name_type        { 1 + t }

msg_or_bool:
| MESSAGE                        { Sorts.emessage }
| BOOLEAN                        { Sorts.eboolean }

/* state_type:
| t=msg_or_bool                  { 0, t }
| INDEX ARROW t=state_type       { let n,k = t in n+1,k } */

msg_type:
| MESSAGE                        { 0 }
| MESSAGE ARROW t=msg_type       { 1 + t }

abs_type:
| t=msg_type                     { 0,t }
| INDEX ARROW t=abs_type         { let i,m = t in i+1,m }

index_arity:
|                                { 0 }
| LPAREN i=INT RPAREN            { i }

declaration_i:
| HASH e=lsymb a=index_arity
                          { Decl.Decl_hash (Some a, e, None) }
| HASH e=lsymb WITH ORACLE f=term
                          { Decl.Decl_hash (None, e, Some f) }
| AENC e=lsymb COMMA d=lsymb COMMA p=lsymb
                          { Decl.Decl_aenc (e, d, p) }
| SENC e=lsymb COMMA d=lsymb
                          { Decl.Decl_senc (e, d) }
| SENC e=lsymb COMMA d=lsymb WITH h=lsymb
                          { Decl.Decl_senc_w_join_hash (e, d, h) }
| SIGNATURE s=lsymb COMMA c=lsymb COMMA p=lsymb
                          { Decl.Decl_sign (s, c, p, None) }
| SIGNATURE s=lsymb COMMA c=lsymb COMMA p=lsymb
  WITH ORACLE f=term   { Decl.Decl_sign (s, c, p, Some f) }
| NAME e=lsymb COLON t=name_type
                          { Decl.Decl_name (e, t) }
| ABSTRACT e=lsymb COLON t=abs_type
                          { let index_arity,message_arity = t in
                            Decl.(Decl_abstract
                                    { name = e;
                                      index_arity=index_arity;
                                      message_arity=message_arity;}) }
| MUTABLE e=lsymb args=opt_arg_list COLON typ=msg_or_bool EQ t=term
                          { Decl.Decl_state (e, args, typ, t) }
| CHANNEL e=lsymb         { Decl.Decl_channel e }
| TERM e=lsymb args=opt_arg_list COLON typ=msg_or_bool EQ t=term
                          { Decl.Decl_macro (e, args, typ, t) }
| PROCESS e=lsymb args=opt_arg_list EQ p=process
                          { Decl.Decl_process (e, args, p) }
| AXIOM s=bsystem f=term
                          { Decl.(Decl_axiom { gname = None;
                                               gsystem = s;
                                               gform = f; }) }
| AXIOM s=bsystem i=lsymb COLON f=term
                          { Decl.(Decl_axiom { gname = Some i;
                                               gsystem = s;
                                               gform = f; }) }
| SYSTEM p=process
                          { Decl.(Decl_system { sname = None;
                                                sprocess = p}) }
| SYSTEM LBRACKET id=lsymb RBRACKET p=process
                          { Decl.(Decl_system { sname = Some id;
                                                sprocess = p}) }

declaration:
| ldecl=loc(declaration_i)                  { ldecl }

declaration_list:
| decl=declaration                        { [decl] }
| decl=declaration decls=declaration_list { decl :: decls }

declarations:
| decls=declaration_list DOT { decls }

tactic_param:
| f=term %prec tac_prec  { TacticsArgs.Theory f }
| i=INT                  { TacticsArgs.Int_parsed i }

tactic_params:
|                                       { [] }
| t=tactic_param                        { [t] }
| t=tactic_param COMMA ts=tactic_params { t::ts }

(*------------------------------------------------------------------*)
rw_mult:
| BANGU  { `Many }
| QMARK  { `Any }
|        { `Once }

rw_dir:
|       { `LeftToRight }
| MINUS { `RightToLeft }

rw_type:
| f=sterm      { `Form f }  

| SLASH t=sterm  { `Expand t }

rw_param:
| m=rw_mult d=loc(rw_dir) t=rw_type  { TacticsArgs.{ rw_mult = m; 
                                                     rw_dir = d; 
                                                     rw_type = t; } }

rw_params:
| l=slist1(rw_param, empty) { l }

rw_in:
|                          { None }
| IN l=slist1(lsymb,COMMA) { Some (`Hyps l) }
| IN STAR                  { Some `All }

(*------------------------------------------------------------------*)
tac_errors:
|                         { [] }
| i=ID                    { [i] }
| i=ID COMMA t=tac_errors { i::t }

(*------------------------------------------------------------------*)
naming_pat:
| UNDERSCORE  { TacticsArgs.Unnamed }
| QMARK       { TacticsArgs.AnyName }
| id=ID       { TacticsArgs.Named id }

and_or_pat:
| LBRACKET s=simpl_pat          ips=slist(simpl_pat, empty)    RBRACKET
                    { TacticsArgs.And (s :: ips) }
| LBRACKET s=simpl_pat PARALLEL ips=slist(simpl_pat, PARALLEL) RBRACKET
                    { TacticsArgs.Or  (s :: ips) }
| LBRACKET RBRACKET { TacticsArgs.Split }

simpl_pat:
| n_ip=naming_pat  { TacticsArgs.SNamed n_ip }
| ao_ip=and_or_pat { TacticsArgs.SAndOr ao_ip }

intro_pat:
| l=loc(SLASHSLASH) { TacticsArgs.Tryauto  (L.loc l)}
| l=loc(SLASHEQUAL) { TacticsArgs.Simplify (L.loc l)}
| l=loc(STAR)       { TacticsArgs.Star     (L.loc l)}
| pat=simpl_pat     { TacticsArgs.Simpl pat }

intro_pat_list:
| l=slist1(intro_pat,empty) { l }

(*------------------------------------------------------------------*)
int:
|i=INT { i }

selector:
| l=slist1(int,COMMA) { l }

tac_formula:
| f=term  %prec tac_prec { f }

as_ip:
| AS ip=simpl_pat { ip }

%inline sel_tac:
| s=selector COLON r=tac { (s,r) }

sel_tacs:
| l=slist1(sel_tac,PARALLEL) { l }

(*------------------------------------------------------------------*)
tac:
  | LPAREN t=tac RPAREN                { t }
  | l=tac SEMICOLON r=tac              { T.AndThen [l;r] }
  | l=tac SEMICOLON LBRACKET sls=sel_tacs RBRACKET
                                       { T.AndThenSel (l,sls) }
  | l=tac SEMICOLON sl=sel_tac %prec tac_prec
                                       { T.AndThenSel (l,[sl]) }
  | BY t=tac %prec tac_prec            { T.By t }
  | l=tac PLUS r=tac                   { T.OrElse [l;r] }
  | TRY l=tac                          { T.Try l }
  | REPEAT t=tac                       { T.Repeat t }
  | id=ID t=tactic_params              { T.Abstract (id,t) }

  (* Special cases for tactics whose names are not parsed as ID
   * because they are reserved. *)

  | LEFT                               { T.Abstract ("left",[]) }
  | RIGHT                              { T.Abstract ("right",[]) }

  | INTRO p=intro_pat_list             { T.Abstract
                                           ("intro",[TacticsArgs.IntroPat p]) }

  | t=tac DARROW p=intro_pat_list      { T.AndThen
                                           [t;T.Abstract
                                                ("intro",[TacticsArgs.IntroPat p])] }

  | DESTRUCT i=lsymb                   { T.Abstract
                                           ("destruct",[TacticsArgs.String_name i]) }

  | DESTRUCT i=lsymb AS p=and_or_pat   { T.Abstract
                                           ("destruct",[TacticsArgs.String_name i;
                                                        TacticsArgs.AndOrPat p]) }

  | DEPENDS args=tactic_params         { T.Abstract ("depends",args) }
  | DEPENDS args=tactic_params BY t=tac
                                       { T.AndThenSel
                                           (T.Abstract ("depends",args), 
                                            [[1], t]) }

  | EXISTS t=tactic_params             { T.Abstract
                                          ("exists",t) }
  | NOSIMPL t=tac                      { T.Modifier
                                          ("nosimpl", t) }
  | CYCLE i=INT                        { T.Abstract
                                         ("cycle",[TacticsArgs.Int_parsed i]) }
  | CYCLE MINUS i=INT                  { T.Abstract
                                         ("cycle",[TacticsArgs.Int_parsed (-i)]) }
  | CHECKFAIL t=tac EXN ts=tac_errors  { T.CheckFail
                                         (T.tac_error_of_strings  ts,t) }

  | REVERT ids=slist1(lsymb, empty)     
    { let ids = List.map (fun id -> TacticsArgs.String_name id) ids in
      T.Abstract ("revert", ids) }

  | GENERALIZE ids=slist1(sterm, empty)     
    { let ids = List.map (fun id -> TacticsArgs.Theory id) ids in
      T.Abstract ("generalize", ids) }

  | CLEAR ids=slist1(lsymb, empty)     
    { let ids = List.map (fun id -> TacticsArgs.String_name id) ids in
      T.Abstract ("clear", ids) }

  | ASSERT p=tac_formula ip=as_ip?
    { let ip = match ip with
        | None -> []
        | Some ip -> [TacticsArgs.SimplPat ip] in
      T.Abstract ("assert", TacticsArgs.Theory p::ip) }

  | USE i=lsymb ip=as_ip?
    { let ip = match ip with
        | None -> []
        | Some ip -> [TacticsArgs.SimplPat ip] in
      T.Abstract ("use", ip @ [TacticsArgs.String_name i]) }

  | USE i=lsymb WITH t=tactic_params ip=as_ip?
    { let ip : TacticsArgs.parser_arg list = match ip with
        | None -> []
        | Some ip -> [TacticsArgs.SimplPat ip] in
      T.Abstract ("use", ip @ [TacticsArgs.String_name i] @ t) }

  | REWRITE p=rw_params w=rw_in
    { T.Abstract ("rewrite", [TacticsArgs.RewriteIn (p, w)]) }

  | DDH i1=lsymb COMMA i2=lsymb COMMA i3=lsymb  { T.Abstract
                                          ("ddh",
                                           [TacticsArgs.String_name i1;
					                                  TacticsArgs.String_name i2;
					                                  TacticsArgs.String_name i3;
				                                   ]) }

  | HELP                               { T.Abstract
                                          ("help",
                                           []) }

  | HELP i=lsymb                          { T.Abstract
                                          ("help",
                                           [TacticsArgs.String_name i]) }

  | HELP h=help_tac
   { T.Abstract ("help",[TacticsArgs.String_name h]) }

(* A few special cases for tactics whose names are not parsed as ID
 * because they are reserved. *)
help_tac_i:
| LEFT       { "left"}     
| RIGHT      { "right"}    
| EXISTS     { "exists"}    
| USE        { "use"}      
| REWRITE    { "rewrite"}  
| REVERT     { "revert"}  
| GENERALIZE { "generalize"}  
| DEPENDS    { "depends"}  
| DDH        { "ddh"}      
| ASSERT     { "assert"}   
| DESTRUCT   { "destruct"} 
| INTRO      { "intro"} 

help_tac:
| l=loc(help_tac_i) { l }

qed:
| QED                                 { () }

abort:
| ABORT                               { () }


undo:
| UNDO i=INT DOT                      { i }

tactic:
| t=tac DOT                           { t }

equiv:
| ei=term                 { [ei] }
| ei=term COMMA eis=equiv { ei::eis }

equiv_form:
| LBRACKET f=term RBRACKET      { Prover.PReach f }
| e=equiv            { Prover.PEquiv e }
/* | LPAREN f=equiv_form RPAREN       { f } */
| f=equiv_form ARROW f0=equiv_form { Prover.PImpl (f,f0) }

args:
|                                         { [] }
| LPAREN vs0=arg_list RPAREN vs=args { vs0 @ vs }

system:
|                         { SystemExpr.(P_SimplePair default_system_name) }
| LBRACKET LEFT RBRACKET  { SystemExpr.(P_Single (P_Left default_system_name)) }
| LBRACKET RIGHT RBRACKET { SystemExpr.(P_Single (P_Right default_system_name)) }
| LBRACKET NONE  COMMA i=lsymb RBRACKET { SystemExpr.(P_SimplePair i) }
| LBRACKET LEFT  COMMA i=lsymb RBRACKET { SystemExpr.(P_Single (P_Left i)) }
| LBRACKET RIGHT COMMA i=lsymb RBRACKET { SystemExpr.(P_Single (P_Right i)) }

bsystem:
|                            { SystemExpr.(P_SimplePair default_system_name) }
| LBRACKET i=lsymb RBRACKET  { SystemExpr.(P_SimplePair i) }

single_system:
| LBRACKET LEFT RBRACKET  { SystemExpr.(P_Left default_system_name)}
| LBRACKET RIGHT RBRACKET { SystemExpr.(P_Right default_system_name)}
| LBRACKET LEFT  COMMA i=lsymb RBRACKET { SystemExpr.(P_Left i) }
| LBRACKET RIGHT COMMA i=lsymb RBRACKET { SystemExpr.(P_Right i)}

gname:
| i=lsymb    { P_named i }
| UNDERSCORE { P_unknown }

goal_i:
| GOAL s=system n=gname args=args COLON f=term DOT
    { let f_i = Theory.ForAll (args, f) in
      let fa = L.mk_loc (L.loc f) f_i in
      Prover.Gm_goal (n, P_trace_goal (s, fa)) }

| EQUIV n=gname env=args COLON f=loc(equiv_form) DOT
                 { Prover.Gm_goal (n, P_equiv_goal (env, f)) }
| EQUIV n=gname DOT
                 { Prover.Gm_goal
                     (n, P_equiv_goal_process
                                   (SystemExpr.(P_Left  default_system_name),
			                              SystemExpr.(P_Right default_system_name))) }
| EQUIV b1=single_system b2=single_system n=gname DOT
                 { Prover.Gm_goal
                     (n, Prover.P_equiv_goal_process (b1, b2))}

| PROOF          { Prover.Gm_proof }

goal:
| goal=loc(goal_i) { goal }

option_param:
| TRUE  { Config.Param_bool true  }
| FALSE { Config.Param_bool false }
| n=ID  {
        if n = "true" then (Config.Param_bool true)
        else if n = "false" then (Config.Param_bool false)
        else Config.Param_string n   }
| i=INT { Config.Param_int i      }

set_option:
| SET n=ID EQ param=option_param DOT { (n, param) }

interactive :
| set=set_option     { Prover.ParsedSetOption set }
| decls=declarations { Prover.ParsedInputDescr decls }
| u=undo             { Prover.ParsedUndo u }
| tac=tactic         { Prover.ParsedTactic tac }
| qed                { Prover.ParsedQed }
| abort              { Prover.ParsedAbort }
| g=goal             { Prover.ParsedGoal g }
| EOF                { Prover.EOF }
