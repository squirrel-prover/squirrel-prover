%{
  module L  = Location
  module T  = Tactics

  let sloc startpos endpos s =
    let loc = L.make startpos endpos in
    L.mk_loc loc s
%}

%token <int> INT
%token <string> ID   /* general purpose identifier */
%token <string> INFIXSYMB   /* infix function symbols */
%token <string> BANG
%token AT PRED
%token LPAREN RPAREN
%token LBRACKET RBRACKET
%token LANGLE RANGLE
%token AND OR NOT TRUE FALSE HAPPENS
%token EQ NEQ GEQ LEQ COMMA SEMICOLON COLON PLUS MINUS
%token XOR STAR UNDERSCORE QMARK TICK
%token LET IN IF THEN ELSE FIND SUCHTHAT
%token DIFF LEFT RIGHT SEQ 
%token NEW OUT PARALLEL NULL
%token CHANNEL PROCESS HASH AENC SENC SIGNATURE NAME ABSTRACT TYPE
%token MUTABLE SYSTEM SET
%token INIT INDEX MESSAGE BOOLEAN TIMESTAMP ARROW RARROW ASSIGN
%token EXISTS FORALL QUANTIF GOAL EQUIV DARROW DEQUIVARROW AXIOM
%token DOT SLASH BANGU SLASHEQUAL SLASHSLASH ATSLASH
%token TIME WHERE WITH ORACLE EXN
%token LARGE NAMEFIXEDLENGTH
%token TRY CYCLE REPEAT NOSIMPL HELP DDH CHECKFAIL ASSERT USE 
%token REWRITE REVERT CLEAR GENERALIZE DEPENDS APPLY
%token BY INTRO AS DESTRUCT
%token PROOF QED UNDO ABORT
%token EOF

%nonassoc QUANTIF
%right ARROW
%right DARROW
%right DEQUIVARROW
%left AND OR

%nonassoc TRUE SEQ PRED NOT LPAREN INIT ID HAPPENS FALSE DIFF

%nonassoc EQ NEQ GEQ LEQ LANGLE RANGLE

%nonassoc empty_else
%nonassoc ELSE

%left INFIXSYMB 

%left XOR

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

%inline lloc(X):
| X { L.make $startpos $endpos }

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

| LANGLE t=term COMMA t0=term RANGLE
    { let fsymb = sloc $startpos $endpos "pair" in
      Theory.App (fsymb, [t;t0]) }

/* formula */

| DIFF LPAREN t=term COMMA t0=term RPAREN { Theory.Diff (t,t0) }
| SEQ LPAREN i=ids ARROW t=term RPAREN    { Theory.Seq (i,t) }

| l=loc(NOT) f=sterm                             
    { let fsymb = L.mk_loc (L.loc l) "not" in
      Theory.App (fsymb,[f]) }

| l=lloc(FALSE)  { Theory.App (L.mk_loc l "false",[]) }

| l=lloc(TRUE)   { Theory.App (L.mk_loc l "true",[]) }

| HAPPENS LPAREN ts=slist1(term,COMMA) RPAREN
                                          { Theory.Happens ts }

/* timestamp */

| PRED LPAREN ts=term RPAREN             { Theory.Tpred ts }
| INIT                                   { Theory.Tinit }

%inline infix_s:
| AND         { "&&"  }
| OR          { "||"   }
| s=INFIXSYMB { s }
| XOR         { "xor"  }
| DARROW      { "=>" }

/* ambiguous term */
term_i:
| f=sterm_i                                  { f }
| id=lsymb terms=term_list1                  { Theory.App (id, terms) }
| id=lsymb AT ts=term                        { Theory.AppAt (id,[],ts) }
| id=lsymb terms=term_list1 AT ts=term       { Theory.AppAt (id,terms,ts) }

| t=term s=loc(infix_s) t0=term             { Theory.App (s, [t;t0]) }

| f=term l=lloc(DEQUIVARROW) f0=term
    { let loc = L.make $startpos $endpos in
      let fi = L.mk_loc l "=>" in
      let fa = L.mk_loc l "&&"  in
      Theory.App (fa, [L.mk_loc loc (Theory.App (fi, [f;f0]));
                       L.mk_loc loc (Theory.App (fi, [f0;f]))]) }
 
| IF b=term THEN t=term t0=else_term
    { let fsymb = sloc $startpos $endpos "if" in
      Theory.App (fsymb,  [b;t;t0]) }

| FIND is=indices SUCHTHAT b=term IN t=term t0=else_term
                                          { Theory.Find (is,b,t,t0) }

| f=term o=ord f0=term                    { Theory.Compare (o,f,f0) }

| EXISTS LPAREN vs=arg_list RPAREN sep f=term %prec QUANTIF
                                 { Theory.Exists (vs,f)  }

| FORALL LPAREN vs=arg_list RPAREN sep f=term %prec QUANTIF
                                 { Theory.ForAll (vs,f)  }

| EXISTS a=arg sep f=term %prec QUANTIF
                                 { Theory.Exists (a,f)  }

| FORALL a=arg sep f=term %prec QUANTIF
                                 { Theory.ForAll (a,f)  }

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

arg:
| is=ids COLON k=p_ty                     { List.map (fun x -> x,k) is }

arg_list:
|                                         { [] }
| is=ids COLON k=p_ty                     { List.map (fun x -> x,k) is }
| is=ids COLON k=p_ty COMMA args=arg_list { List.map (fun x -> x,k) is @ args }

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

colon_ty:
| COLON t=p_ty { t }

process_i:
| NULL                             { Process.Null }
| LPAREN ps=processes_i RPAREN     { ps }
| id=lsymb terms=term_list         { Process.Apply (id,terms) }
| id=lsymb COLON p=process         { Process.Alias (p,id) }

| NEW id=lsymb ty=colon_ty? SEMICOLON p=process
    { let ty = match ty with
        | Some ty -> ty
        | None -> L.mk_loc (L.loc id) Theory.P_message 
      in
      Process.New (id,ty,p) }

| IN LPAREN c=lsymb COMMA id=lsymb RPAREN p=process_cont
    { Process.In (c,id,p) }

| OUT LPAREN c=lsymb COMMA t=term RPAREN p=process_cont
    { Process.Out (c,t,p) }

| IF f=term THEN p=process p0=else_process
    { Process.Exists ([],f,p,p0) }

| FIND is=indices SUCHTHAT f=term IN p=process p0=else_process
    { Process.Exists (is,f,p,p0) }

| LET id=lsymb ty=colon_ty? EQ t=term IN p=process
    { Process.Let (id,t,ty,p) }

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
| ty=p_ty                     { 0,ty }
| INDEX ARROW t=name_type     { let i,ty = t in
                                1 + i,ty }

ty_var:
| TICK id=lsymb     { id }

index_arity:
|                                { 0 }
| LPAREN i=INT RPAREN            { i }

p_ty_i:
| MESSAGE      { Theory.P_message }
| INDEX        { Theory.P_index }
| TIMESTAMP    { Theory.P_timestamp }
| BOOLEAN      { Theory.P_boolean }
| tv=ty_var    { Theory.P_tvar tv }
| l=lsymb      { Theory.P_tbase l }

p_ty:
| ty=loc(p_ty_i) { ty }

fun_ty:
| l=slist1(p_ty,ARROW)      { l }

/* crypto assumption typed space */
c_ty:
| l=lsymb COLON ty=p_ty { Decl.{ cty_space = l; 
                                 cty_ty    = ty; } }

/* crypto assumption typed space */
c_tys:
| WHERE list=slist1(c_ty, empty) { list }
|                                { [] }

ty_args:
|                                          { [] }
| LBRACKET ids=slist1(ty_var,empty) RBRACKET { ids }

bty_info:
| NAMEFIXEDLENGTH { Symbols.Ty_name_fixed_length }
| LARGE           { Symbols.Ty_large }

bty_infos:
| LBRACKET l=slist(bty_info,COMMA) RBRACKET { l }
|                                           { [] }

lsymb_decl:
| id=lsymb                       { `Prefix, id }
| LPAREN s=loc(INFIXSYMB) RPAREN { `Infix, s }

declaration_i:
| HASH e=lsymb a=index_arity ctys=c_tys
                          { Decl.Decl_hash (Some a, e, None, ctys) }

| HASH e=lsymb WITH ORACLE f=term
                          { Decl.Decl_hash (None, e, Some f, []) }

| AENC e=lsymb COMMA d=lsymb COMMA p=lsymb ctys=c_tys
                          { Decl.Decl_aenc (e, d, p, ctys) }

| SENC e=lsymb COMMA d=lsymb ctys=c_tys
                          { Decl.Decl_senc (e, d, ctys) }

| SENC e=lsymb COMMA d=lsymb WITH HASH h=lsymb
                          { Decl.Decl_senc_w_join_hash (e, d, h) }

| SIGNATURE s=lsymb COMMA c=lsymb COMMA p=lsymb ctys=c_tys
                          { Decl.Decl_sign (s, c, p, None, ctys) }

| SIGNATURE s=lsymb COMMA c=lsymb COMMA p=lsymb
  WITH ORACLE f=term       
                          { Decl.Decl_sign (s, c, p, Some f, []) }

| DDH g=lsymb COMMA ei=lsymb_decl ctys=c_tys
    { let e, f_info = ei in
      Decl.Decl_ddh (g,(f_info,e), ctys) }

| NAME e=lsymb COLON t=name_type
                          { let a,ty = t in 
                            Decl.Decl_name (e, a, ty) }

| TYPE e=lsymb infos=bty_infos 
                          { Decl.Decl_bty { bty_name = e; bty_infos = infos; } }

| ABSTRACT e=lsymb_decl a=ty_args COLON t=fun_ty
    { let symb_type, name = e in
      Decl.(Decl_abstract
              { name      = name;
                symb_type = symb_type;
                ty_args   = a;
                abs_tys   = t; }) }

| MUTABLE e=lsymb args=opt_arg_list COLON typ=p_ty EQ t=term
                          { Decl.Decl_state (e, args, typ, t) }

| CHANNEL e=lsymb         { Decl.Decl_channel e }

/* | TERM e=lsymb args=opt_arg_list COLON typ=p_ty EQ t=term */
/*                           { Decl.Decl_macro (e, args, typ, t) } */

| PROCESS e=lsymb args=opt_arg_list EQ p=process
                          { Decl.Decl_process (e, args, p) }

| AXIOM g=goal_reach { Decl.Decl_axiom g }

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
| f=sterm        { `Form f }  
| SLASH t=sterm  { `Expand t }

expnd_type:
| ATSLASH t=sterm  { `Expand t }

rw_item:
| m=rw_mult d=loc(rw_dir) t=rw_type  { TacticsArgs.{ rw_mult = m; 
                                                     rw_dir = d; 
                                                     rw_type = t; } }

expnd_item:
| d=loc(rw_dir) t=expnd_type  { TacticsArgs.{ rw_mult = `Once; 
                                              rw_dir = d; 
                                              rw_type = t; } }


rw_arg:
| r=rw_item { TacticsArgs.R_item r }
| s=s_item  { TacticsArgs.R_s_item s }

rw_args:
| l=slist1(rw_arg, empty) { l }

rw_in:
|                          { None }
| IN l=slist1(lsymb,COMMA) { Some (`Hyps l) }
| IN STAR                  { Some `All }

apply_in:
|             { None }
| IN id=lsymb { Some id }

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

ip_rw_dir:
| ARROW  { `LeftToRight }
| RARROW { `RightToLeft }

simpl_pat:
| n_ip=naming_pat  { TacticsArgs.SNamed n_ip }
| ao_ip=and_or_pat { TacticsArgs.SAndOr ao_ip }
| d=loc(ip_rw_dir) { TacticsArgs.Srewrite d }

s_item:
| l=loc(SLASHSLASH) { TacticsArgs.Tryauto  (L.loc l)}
| l=loc(SLASHEQUAL) { TacticsArgs.Simplify (L.loc l)}

intro_pat:
| s=s_item      { TacticsArgs.SItem (s) }
| l=loc(STAR)   { TacticsArgs.Star  (L.loc l)}
| l=loc(RANGLE) { TacticsArgs.StarV (L.loc l)}
| pat=simpl_pat { TacticsArgs.Simpl pat }
| e=expnd_item  { TacticsArgs.SExpnd e }

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
  | TIME t=tac  %prec tac_prec         { T.Time t }
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

  | REWRITE p=rw_args w=rw_in
    { T.Abstract ("rewrite", [TacticsArgs.RewriteIn (p, w)]) }

  | APPLY t=sterm w=apply_in
    { T.Abstract ("apply", [TacticsArgs.ApplyIn (t, w)]) }

  | DDH g=lsymb COMMA i1=lsymb COMMA i2=lsymb COMMA i3=lsymb 
    { T.Abstract
        ("ddh",
         [TacticsArgs.String_name g;
          TacticsArgs.String_name i1;
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
| APPLY      { "apply"}  
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
|                                    { [] }
| LPAREN vs0=arg_list RPAREN vs=args { vs0 @ vs }

system:
|                           { SystemExpr.(P_SimplePair default_system_name) }
| LBRACKET LEFT RBRACKET    { SystemExpr.(P_Single (P_Left default_system_name)) }
| LBRACKET RIGHT RBRACKET   { SystemExpr.(P_Single (P_Right default_system_name)) }
| LBRACKET i=lsymb RBRACKET { SystemExpr.(P_SimplePair i) }
| LBRACKET LEFT  COLON i=lsymb RBRACKET { SystemExpr.(P_Single (P_Left i)) }
| LBRACKET RIGHT COLON i=lsymb RBRACKET { SystemExpr.(P_Single (P_Right i)) }

single_system:
| LBRACKET LEFT RBRACKET  { SystemExpr.(P_Left default_system_name)}
| LBRACKET RIGHT RBRACKET { SystemExpr.(P_Right default_system_name)}
| LBRACKET LEFT  COMMA i=lsymb RBRACKET { SystemExpr.(P_Left i) }
| LBRACKET RIGHT COMMA i=lsymb RBRACKET { SystemExpr.(P_Right i)}

gname:
| i=lsymb    { P_named i }
| UNDERSCORE { P_unknown }

goal_reach:
| s=system n=gname tyvs=ty_args args=args COLON f=term 
    { let goal_cnt = Decl.{ g_system = s; 
                            g_tyvars = tyvs; 
                            g_vars = args; 
                            g_form = f; } 
      in
      n, goal_cnt }

goal_i:
| GOAL g=goal_reach DOT
    { let n, goal_cnt = g in
      Prover.Gm_goal (n, Prover.P_trace_goal goal_cnt) }

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
