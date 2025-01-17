%{
  open Squirrelcore
  module T  = Tactics
  module SE = SystemExpr

  module L = Location

  let sloc startpos endpos s =
    let loc = L.make startpos endpos in
    L.mk_loc loc s

  let mk_abstract loc s args =
    Tactics.Abstract (L.mk_loc loc s, args)

  let top_path = []
%}

%token <int> INT
%token <string> LID              /* identifier started by a lower-case character */
%token <string> UID              /* identifier started by an upper-case character */
%token <string> QUOTED_STRING    /* a quoted string (the enclosing quotes '"'
                                    have already been stripped) */
%token <string> LEFTINFIXSYMB    /* left infix function symbols */
%token <string> RIGHTINFIXSYMB   /* right infix function symbols */
%token <string> BANG

%token AT TRANS FRESH
%token LPAREN RPAREN
%token LBRACKET RBRACKET
%token LBRACE RBRACE
%token LANGLE RANGLE (*LANGLECOLON*) LQUOTED RQUOTED
%token GAND GOR AND OR NOT TRUE FALSE 
%token EQ NEQ GEQ LEQ COMMA SEMICOLON COLON PLUS MINUS COLONEQ
%token XOR STAR UNDERSCORE QMARK TICK BACKTICK
%token LLET LET IN IF THEN ELSE FIND SUCHTHAT
%token TILDE DIFF SEQ
%token NEW OUT PARALLEL NULL
%token CHANNEL PROCESS
%token HASH AENC SENC SIGNATURE ACTION NAME ABSTRACT OP PREDICATE
%token TYPE FUN
%token MUTABLE SYSTEM SET
%token LEMMA THEOREM
%token INDEX MESSAGE BOOL BOOLEAN TIMESTAMP ARROW RARROW
%token EXISTS FORALL QUANTIF EQUIV DARROW DEQUIVARROW AXIOM
%token UEXISTS UFORALL
%token LOCAL GLOBAL
%token DOT SLASH BANGU SLASHEQUAL SLASHSLASH SLASHSLASHEQUAL ATSLASH
%token SHARP DOLLAR SHARPINIT
%token GAME VAR RND RETURN
%token TIME WHERE WITH ORACLE EXN
%token PERCENT
%token TRY CYCLE REPEAT NOSIMPL HELP DDH CDH GDH CHECKFAIL ASSERT GHAVE HAVE WEAK USE
%token REDUCE SIMPL AUTO
%token REWRITE REVERT CLEAR GENERALIZE DEPENDENT DEPENDS APPLY LOCALIZE CASE
%token SPLITSEQ CONSTSEQ MEMSEQ
%token BY FA CS INTRO AS DESTRUCT REMEMBER INDUCTION CRYPTO DEDUCE
%token PROOF QED RESET UNDO ABORT HINT
%token TACTIC
%token RENAME GPRF GCCA
%token INCLUDE PRINT SEARCH PROF
%token NAMESPACE END OPEN CLOSE
%token SMT
%token TERMINAL
%token EOF

%nonassoc IN
%nonassoc QUANTIF
%right ARROW
%right DARROW 
%right DEQUIVARROW
%right AND OR
%right GAND GOR

%nonassoc EQ NEQ GEQ LEQ LANGLE RANGLE

%nonassoc empty_else
%nonassoc ELSE

%left SHARP

%right RIGHTINFIXSYMB
%left  LEFTINFIXSYMB

%left XOR

%nonassoc AT

%nonassoc tac_prec

%nonassoc BY
%left PLUS MINUS
%left STAR
%right SEMICOLON
%nonassoc REPEAT
%nonassoc TRY
%nonassoc NOSIMPL

(*------------------------------------------------------------------*)
(* start symbols and their type declarations *)

%start declarations
%start top_formula
/* %start system_expr */ (* Menhir bug *)
%start top_process
%start interactive
%start top_proofmode
%start interactive_or_undo
%start top_proofmode_or_undo
%start top_global_formula
%type <Decl.declarations> declarations
%type <Typing.term> top_formula
%type <Typing.global_formula> top_global_formula
%type <SystemExpr.Parse.t> system_expr
%type <Process.Parse.t> top_process
%type <ProverLib.input> interactive
%type <ProverLib.input> top_proofmode
%type <ProverLib.input_or_undo> interactive_or_undo
%type <ProverLib.input_or_undo> top_proofmode_or_undo
%type <ProverTactics.AST.t> tac

(*------------------------------------------------------------------*)
(* type declarations of some inner symbols, to help debugging *)
%type <string L.located> lsymb_gen
%type <Symbols.p_path> spath_gen

%%

(*------------------------------------------------------------------*)
(* Locations *)
%inline loc(X):
| x=X {
    { L.pl_desc = x;
      L.pl_loc  = L.make $startpos $endpos;
    }
  }

%inline lloc(X):
| X { L.make $startpos $endpos }

(*------------------------------------------------------------------*)
(* Lists *)

%inline empty:
| { () }

%inline slist(X, S):
| l=separated_list(S, X) { l }

%inline slist1(X, S):
| l=separated_nonempty_list(S, X) { l }

(* -------------------------------------------------------------------- *)
__rlist1(X, S):                         (* left-recursive *)
| x=X { [x] }
| xs=__rlist1(X, S) S x=X { x :: xs }

%inline rlist0(X, S):
| /* empty */     { [] }
| xs=rlist1(X, S) { xs }

%inline rlist1(X, S):
| xs=__rlist1(X, S) { List.rev xs }

(*------------------------------------------------------------------*)
%inline paren(X):
| LPAREN x=X RPAREN { x }

(*------------------------------------------------------------------*)
(* DH flags *)
dh_flag:
| DDH { Symbols.OpData.DH_DDH }
| CDH { Symbols.OpData.DH_CDH }
| GDH { Symbols.OpData.DH_GDH }

dh_flags:
| l=slist1(dh_flag, COMMA) { l }

(*------------------------------------------------------------------*)
/* parse a quoted string, where the enclosing quotes '"' have been
   stripped */
quoted_string:
| s=loc(QUOTED_STRING) { s }

(*------------------------------------------------------------------*)
(* Identifiers and paths *)

(* lower or upper-case identifier *)
%inline id:
| id=LID { id }
| id=UID { id }

(*------------------------------------------------------------------*)
(* lower-case symbol *)
%inline llsymb:
| id=loc(LID) { id }

(* upper-case symbol *)
%inline lusymb:
| id=loc(UID) { id }

(* lower-case or upper-case symbol *)
%inline lsymb:
| id=loc(id) { id }

(*------------------------------------------------------------------*)
(* namespace path *)
%inline npath:
| l=rlist1(lusymb, DOT) { l }

(*------------------------------------------------------------------*)
%inline gen_path(X):
|               sub=X { [], sub }
| top=npath DOT sub=X { top,sub }

(* path to a lower-case symbol *)
%inline lpath:
| p=gen_path(llsymb) { p }

(* path to an upper-case symbol *)
%inline upath:
| p=gen_path(lusymb) { p }

(* path to a lower-case or upper-case symbol *)
%inline path:
| p=gen_path(lsymb) { p }

(*------------------------------------------------------------------*)
(* auxiliary definition *)
%inline _infix_s:
| PLUS             { "+"   , `Left }
| MINUS            { "-"   , `Left }
| STAR             { "*"   , `Left }
| EQ               { "="   , `Left }
| NEQ              { "<>"  , `Left }
| LEQ              { "<="  , `Left }
| LANGLE           { "<"   , `Left }
| GEQ              { ">="  , `Left }
| RANGLE           { ">"   , `Left }
| AND              { "&&"  , `Left }
| OR               { "||"  , `Left }
| s=LEFTINFIXSYMB  { s     , `Left }
| s=RIGHTINFIXSYMB { s     , `Right }
| XOR              { "xor" , `Left }
| DARROW           { "=>"  , `Left }
| DEQUIVARROW      { "<=>" , `Left }

(* infix symbol with fixity information *)
%inline infix_s:
| s=loc(_infix_s) 
  {
    let str, i = L.unloc s in
    ( L.mk_loc (L.loc s) str, i )
  }

%inline infix_s0:
| s=infix_s { fst s }

(*------------------------------------------------------------------*)
ty_args:
| LBRACKET ids=slist1(ty,COMMA) RBRACKET { ids }

(*------------------------------------------------------------------*)
(* Terms *)

/* non-ambiguous term */
sterm_i:
| i=loc(int)                      { Typing.Int i }
| s=quoted_string                 { Typing.String s }
| path=spath_gen ty_args=ty_args? se_args=se_args?   { Typing.Symb {path; ty_args; se_args; } }
| UNDERSCORE                      { Typing.Tpat }

| DIFF LPAREN t=term COMMA t0=term RPAREN { Typing.Diff (t,t0) }

| SEQ LPAREN 
  vs=bnd_group_list(lval,ty_tagged) 
  DARROW t=term RPAREN                    { Typing.Quant (Seq,vs,t) }

| l=loc(NOT) f=sterm
    { let fsymb = L.mk_loc (L.loc l) "not" in
      Typing.mk_app_i (Typing.mk_symb ([],fsymb)) [f] }

| l=lloc(FALSE)  { Typing.mk_symb_i (top_path, L.mk_loc l "false") }

| l=lloc(TRUE)   { Typing.mk_symb_i (top_path, L.mk_loc l "true") }

| l=paren(slist1(term,COMMA))
    { match l with
      | [t] -> L.unloc t
      | _ -> Typing.Tuple l }


%inline quantif:
| EXISTS { Term.Exists }
| FORALL { Term.ForAll }

/* ambiguous term */
term_i:
| f=sterm_i                         { f }

| t=term AT ts=term                 { Typing.AppAt (t, ts) }
| t=sterm l=slist1(sterm,empty)     { Typing.App (t,l) }

| LANGLE t=term COMMA t0=term RANGLE
   { let fsymb = sloc $startpos $endpos "pair" in
     Typing.mk_app_i (Typing.mk_symb (top_path,fsymb)) [t;t0] }

| t=term s=infix_s0 t0=term       
   { Typing.mk_app_i (Typing.mk_symb (top_path,s)) [t;t0] }

| t=term SHARP i=loc(INT)
    { Typing.Proj (i,t) }

| IF b=term THEN t=term t0=else_term
    { let fsymb = sloc $startpos $endpos "if" in
      Typing.mk_app_i (Typing.mk_symb (top_path,fsymb)) [b;t;t0] }

| FIND vs=bnds SUCHTHAT b=term IN t=term t0=else_term
                                 { Typing.Find (vs,b,t,t0) }

| FUN vs=ext_bnds_tagged DARROW f=term
                                 { Typing.Quant (Lambda,vs,f)  }

| q=quantif vs=ext_bnds_tagged COMMA f=term %prec QUANTIF
                                 { Typing.Quant (q,vs,f)  }

| LET v=lsymb ty=colon_ty? EQ t1=term IN t2=term
    { Typing.Let (v,t1,ty,t2) }

| LQUOTED t=term RQUOTED {Typing.Quote t}

/* non-ambiguous term */
%inline else_term:
| %prec empty_else   { let loc = L.make $startpos $endpos in
                       let fsymb = L.mk_loc loc "zero" in
                       Typing.mk_symb (top_path,fsymb) }
| ELSE t=term       { t }

sterm:
| t=loc(sterm_i) { t }

term:
| t=loc(term_i) { t }

(*------------------------------------------------------------------*)
/* simple lvalues: only support variable declarations */
simpl_lval:
| l=loc(UNDERSCORE)  { L.mk_loc (L.loc l) "_x" }
| l=lsymb            { l }

/* full lvalues */
%inline lval:
| l=simpl_lval                          { Typing.L_var l }
| LPAREN ids=slist1(lsymb,COMMA) RPAREN { Typing.L_tuple ids }

(*------------------------------------------------------------------*)
/* Auxiliary:
   Many binders with the same types: `x1,...,xN : type` */
%inline bnd_group(LVAL,TY):
| is=slist1(LVAL,COMMA) COLON k=TY { List.map (fun x -> x,k) is }

/* Auxiliary:
   many binder groups: `x1,...,xN1 : type1, ..., x1,...,xNL : typeL */
%inline bnd_group_list(LVAL,TY):
| args=slist1(bnd_group(LVAL,TY),COMMA) { List.flatten args }

(*------------------------------------------------------------------*)
/* Auxiliary: a single binder declarations for variables */
%inline bnd:
| LPAREN l=bnd_group_list(simpl_lval,ty) RPAREN { l }
/* many binders, grouped  */

| x=simpl_lval    { [x, L.mk_loc (L.loc x) Typing.P_ty_pat] }
/* single binder `x`, unspecified type */

/* Many binder declarations, strict version
   for use when binder declarations are followed by COLON or COMMA. */
bnds_strict:
| l=slist(bnd, empty) { List.flatten l }

/* Many binder declarations, non-strict version with some added variants. */
bnds:
| bnds_strict                     { $1 }
| l=bnd_group_list(simpl_lval,ty) { l }

(*------------------------------------------------------------------*)
multi_term_bnd:
| LBRACE se_v=se_var COLON l=bnds RBRACE { se_v, l }

multi_term_bnds:
| l=slist(multi_term_bnd, empty) { l }

(*------------------------------------------------------------------*)
/* variable tags */
var_tags:
|                                             { []   }
| LBRACKET tags=slist1(lsymb, COMMA) RBRACKET { tags }

/* type with tags */
ty_tagged:
| k=ty tags=var_tags {k,tags}

(*------------------------------------------------------------------*)
/* Auxiliary: a single binder declarations with tags */
%inline bnd_tagged:
/* many binders, grouped  */
| LPAREN l=bnd_group_list(simpl_lval,ty_tagged) RPAREN { l }

/* single binder `x`, no argument */
| x=simpl_lval    { [x, (L.mk_loc (L.loc x) Typing.P_ty_pat, [])] }

/* Many binder declarations with tags. */
bnds_tagged:
| l=slist(bnd_tagged, empty) { List.flatten l }

(*------------------------------------------------------------------*)
/* Auxiliary: a single binder declarations with tags with full lvalues */
%inline ext_bnd_tagged:
/* many binders, grouped  */
| LPAREN l=bnd_group_list(lval,ty_tagged) RPAREN { l }

/* single binder `x`, no argument */
| x=simpl_lval    { [Typing.L_var x, (L.mk_loc (L.loc x) Typing.P_ty_pat, [])] }

/* Many binder declarations with tags (see bnds_strict). */
ext_bnds_tagged_strict:
| l=slist(ext_bnd_tagged, empty)   { List.flatten l }

ext_bnds_tagged:
| ext_bnds_tagged_strict           { $1 }
| v=simpl_lval COLON ty=ty_tagged  { [Typing.L_var v, ty] }

(*------------------------------------------------------------------*)
/* System variables binders */

/* System variable information (i.e. a tag).
  Currently, a **single** system tag is a **list** of symbols
  (e.g. `pair`, of `like P`). */
%inline se_info:
| i=slist1(lsymb,empty) { i }

/* a list of system infos */
%inline se_infos:
| LBRACKET l=slist(se_info,COMMA) RBRACKET { l }

/* the "type" of a system variable binder */
se_ty:
| SYSTEM i=se_infos?  { Utils.odflt [] i }

/* A group of system variables binders, enclosed in curcly bracket `{ ... }` */
%inline se_bnds_group:
| LBRACE l=bnd_group_list(se_var,se_ty) RBRACE { l }
/* many binders, grouped  */

/* Several groups of system variable binders. */
%inline se_bnds:
| l=slist(se_bnds_group, empty) { List.flatten l }

(*------------------------------------------------------------------*)
top_formula:
| f=term EOF                    { f }

(*------------------------------------------------------------------*)
(* Processes *)

top_process:
| p=process EOF                    { p }

colon_ty:
| COLON t=ty { t }

(*concrete_term:
| LANGLECOLON t=term { t }*)


(* identifier with '$' allowed at the beginning or end *) 
%inline alias_name:
| s=id { s }
| DOLLAR s=id { "$" ^ s }
| s=id DOLLAR { "$" ^ s }

process_i:
| NULL                               { Process.Parse.Null }
| LPAREN ps=processes_i RPAREN       { ps }
| id=loc(alias_name) COLON p=process { Process.Parse.Alias (p,id) }

| NEW id=lsymb ty=colon_ty? SEMICOLON p=process
    { let ty = match ty with
        | Some ty -> ty
        | None -> L.mk_loc (L.loc id) Typing.P_message
      in
      Process.Parse.New (id,ty,p) }

| IN LPAREN c=path COMMA id=lsymb RPAREN p=process_cont
    { Process.Parse.In (c,id,p) }

| OUT LPAREN c=path COMMA t=term RPAREN p=process_cont
    { Process.Parse.Out (c,t,p) }

| IF f=term THEN p=process p0=else_process
    { Process.Parse.Exists ([],f,p,p0) }

| FIND is=opt_indices SUCHTHAT f=term IN p=process p0=else_process
    { Process.Parse.Exists (is,f,p,p0) }

| LET id=lsymb ty=colon_ty? EQ t=term IN p=process
    { Process.Parse.Let (id,t,ty,p) }

| id=path terms=slist(sterm,empty)   { Process.Parse.Apply (id,terms) }
(* we have to use a slist(sterm,empty) while we want to just parse a
tuple (t1,...,tn), to avoid conflicts with the next line *)

| id=path args=slist(sterm,empty) COLONEQ t=term p=process_cont
    { Process.Parse.Set (id,args,t,p) }

| s=loc(BANG) p=process { Process.Parse.Repl (s,p) }

process:
| p=loc(process_i) { p }

processes_i:
| p=process_i                             { p }
| p=process PARALLEL ps=loc(processes_i)  { Process.Parse.Parallel (p,ps) }

processes:
| p=loc(processes_i) { p }

process_cont:
|                                { let loc = L.make $startpos $endpos in
                                   L.mk_loc loc Process.Parse.Null }
| SEMICOLON p=process            { p }

else_process:
| %prec empty_else               { let loc = L.make $startpos $endpos in
                                   L.mk_loc loc Process.Parse.Null }
| ELSE p=process                 { p }

opt_indices:
|                                   { [] }
| id=lsymb                          { [id] }
| id=lsymb COMMA ids=opt_indices    { id::ids }

(*------------------------------------------------------------------*)
/* type variable */
ty_var:
| TICK id=lsymb     { id }

(*------------------------------------------------------------------*)
%inline _tick_uid:
| TICK s=UID { "'" ^ s }

/* e.g. ['P] or ['Q] */
%inline tick_uid:
| s=loc(_tick_uid) { s }

/* system expression variable */
se_var:
| ll=lloc(SET)   { L.mk_loc ll "set" }
| ll=lloc(EQUIV) { L.mk_loc ll "equiv" }
| id=lsymb       { id }
| id=tick_uid    { id }

(*------------------------------------------------------------------*)
/* general types */

ty_i:
| ty=sty_i                          { ty }
| t1=ty ARROW t2=ty                 { Typing.P_fun (t1, t2) }
| t1=sty STAR tys=slist1(sty, STAR) { Typing.P_tuple (t1 :: tys) }

sty_i:
| MESSAGE                        { Typing.P_message }
| INDEX                          { Typing.P_index }
| TIMESTAMP                      { Typing.P_timestamp }
| BOOLEAN                        { Typing.P_boolean }
| BOOL                           { Typing.P_boolean }
| tv=ty_var                      { Typing.P_tvar tv }
| l=path                         { Typing.P_tbase l }
| LPAREN ty=ty_i RPAREN          { ty }
| UNDERSCORE                     { Typing.P_ty_pat }

sty:
| ty=loc(sty_i) { ty }

ty:
| ty=loc(ty_i) { ty }

(*------------------------------------------------------------------*)
/* crypto assumption typed space */
c_ty:
| l=lsymb COLON ty=ty { Decl.{ cty_space = l;
                                      cty_ty    = ty; } }

/* crypto assumption typed space */
c_tys:
| WHERE list=slist1(c_ty, empty) { list }
|                                { [] }

ty_vars:
|                                            { []  }
| LBRACKET ids=slist1(ty_var,empty) RBRACKET { ids }

bty_info:
| info=lsymb { info }

bty_infos:
| LBRACKET l=slist(bty_info,COMMA) RBRACKET { l }
|                                           { [] }

(*------------------------------------------------------------------*)
(* for declarations, a `X` symbol or a parenthesized infix symbol *)
%inline _lsymb_gen_decl(X):
| id=X                     { `Prefix, id }
| LPAREN s=infix_s RPAREN 
          { let s,k = s in
            `Infix k, s }

(* lower- and upper-case *)
%inline lsymb_gen_decl:
| x=_lsymb_gen_decl(lsymb)   { x }

(*------------------------------------------------------------------*)
(* a `X` symbol or a parenthesized infix symbol *)
%inline _lsymb_gen(X):
| x=_lsymb_gen_decl(X)   { snd x }

(* lower- or upper-case *)
%inline lsymb_gen:
| x=_lsymb_gen(lsymb )   { x } 

(*------------------------------------------------------------------*)
(* safe path to a symbol or a infix symbol (e.g. `A.(+)`)  *)
%inline spath_gen:
| x=lsymb_gen                      { (top_path, x) } 
| np=npath DOT x=lsymb_gen         { (np      , x) } 

(*------------------------------------------------------------------*)
%inline projs:
|                                     { None }
| LBRACE l=slist(lsymb, empty) RBRACE { Some l }

(*------------------------------------------------------------------*)
predicate_body:
| EQ form=global_formula { form }

(*------------------------------------------------------------------*)
system_modifier:
| RENAME gf=global_formula
    { Decl.Rename gf }

| GCCA args=bnds_strict COMMA enc=term
    { Decl.CCA (args, enc) }

| GPRF args=bnds_strict COMMA hash=term
    { Decl.PRF (args, hash) }

| REWRITE p=rw_args
    { Decl.Rewrite p }

(*------------------------------------------------------------------*)
(* for now, a single option is enough *)
%inline system_option:
| LBRACKET l=lsymb RBRACKET { Some l }
|                           { None   }

(*------------------------------------------------------------------*)
%inline op_body:
| EQ t=term { `Concrete t }
|           { `Abstract   }

(*------------------------------------------------------------------*)
/* workaround to avoid parser conflicts in predicates declarations */
se_bnds_group_or_empty_group:
| l=se_bnds_group { l  }
| LBRACE RBRACE   { [] }
       
(*------------------------------------------------------------------*)
declaration_i:
| HASH e=lsymb ctys=c_tys
                          { Decl.Decl_hash (e, None, ctys) }

| HASH e=lsymb WITH ORACLE f=term
                          { Decl.Decl_hash (e, Some f, []) }

| AENC e=lsymb COMMA d=lsymb COMMA p=lsymb ctys=c_tys
                          { Decl.Decl_aenc (e, d, p, ctys) }

| SENC e=lsymb COMMA d=lsymb ctys=c_tys
                          { Decl.Decl_senc (e, d, ctys) }

| SENC e=lsymb COMMA d=lsymb WITH HASH h=lpath
                          { Decl.Decl_senc_w_join_hash (e, d, h) }

| SIGNATURE s=lsymb COMMA c=lsymb COMMA p=lsymb ctys=c_tys
                          { Decl.Decl_sign (s, c, p, None, ctys) }

| SIGNATURE s=lsymb COMMA c=lsymb COMMA p=lsymb
  WITH ORACLE f=term
                          { Decl.Decl_sign (s, c, p, Some f, []) }

| h=dh_flags g=lsymb COMMA ei=lsymb_gen_decl ctys=c_tys
    { let e, f_info = ei in
      Decl.Decl_dh (h, g, (f_info, e), None, ctys) }

| h=dh_flags g=lsymb COMMA ei=lsymb_gen_decl COMMA mm=lsymb_gen_decl ctys=c_tys
    { let e, f_info = ei in
      let m, m_info = mm in
      Decl.Decl_dh (h, g, (f_info, e), Some (m_info, m), ctys) }

| NAME e=lsymb COLON ty=ty
                          { Decl.Decl_name (e, ty) }

| ACTION e=lsymb COLON a_arity=int
                          { Decl.Decl_action { a_name = e; a_arity; } }

| TYPE e=lsymb infos=bty_infos
                          { Decl.Decl_bty { bty_name = e; bty_infos = infos; } }

| ABSTRACT e=lsymb_gen_decl tyvars=ty_vars COLON tyo=ty
    { let symb_type, name = e in
      Decl.(Decl_operator
              { op_name      = name;
                op_symb_type = symb_type;
                op_tyargs    = tyvars;
                op_args      = [];
                op_tyout     = Some tyo;
                op_body      = `Abstract }) }

| OP e=lsymb_gen_decl tyvars=ty_vars args=ext_bnds_tagged_strict tyo=colon_ty? body=op_body
    { let symb_type, name = e in
      Decl.(Decl_operator
              { op_name      = name;
                op_symb_type = symb_type;
                op_tyargs    = tyvars;
                op_args      = args;
                op_tyout     = tyo;
                op_body      = body; }) }

| PREDICATE e=lsymb_gen_decl
  tyvars=ty_vars 
  sebnds=se_bnds_group_or_empty_group
  /* workaround to avoid parser conflits: we must have exactly one
     group of system variable binders */
  multi_args=multi_term_bnds
  simpl_args=bnds
  body=predicate_body? 
    { let symb_type, name = e in
      Decl.(Decl_predicate
              { pred_name       = name;
                pred_symb_type  = symb_type;
                pred_tyargs     = tyvars;
                pred_se_args    = sebnds;
                pred_multi_args = multi_args;
                pred_simpl_args = simpl_args;
                pred_body       = body; }) }

| MUTABLE name=lsymb args=bnds_strict out_ty=colon_ty? EQ init_body=term
                          { Decl.Decl_state {name; args; out_ty; init_body; }}

| CHANNEL e=lsymb         { Decl.Decl_channel e }

| PROCESS id=lsymb projs=projs args=bnds EQ proc=process
                          { Decl.Decl_process {id; projs; args; proc} }

|        AXIOM s=local_statement  { Decl.Decl_axiom s }
|  LOCAL AXIOM s=local_statement  { Decl.Decl_axiom s }
| GLOBAL AXIOM s=global_statement { Decl.Decl_axiom s }

/* declares the default system */
| SYSTEM system_option=system_option sprojs=projs p=processes
  { Decl.Decl_system { 
        sname      = None;
        system_option;
        sprojs;
        sprocess   = p; } }

/* declares a named system */
| SYSTEM system_option=system_option sprojs=projs id=lsymb EQ p=processes
   { Decl.Decl_system { 
         sname      = Some id;
         system_option;
         sprojs;
         sprocess   = p} }

 | g=game { Decl.Decl_game g }

 | NAMESPACE n=npath { Decl.Namespace_cmd (Enter n) }
 | END       n=npath { Decl.Namespace_cmd (Exit  n) }
 | OPEN      n=npath { Decl.Namespace_cmd (Open  n) }
 | CLOSE     n=npath { Decl.Namespace_cmd (Close n) }

/* declaration that must always be followed by the terminator symbol `.` */
declaration_no_concat_i:
| TACTIC lsymb EQ tac                     { Decl.Tactic ($2,$4) }

/* system modifiers */
| SYSTEM id=lsymb EQ LBRACKET from_sys=system_expr RBRACKET WITH modifier=system_modifier
    { Decl.(Decl_system_modifier
              { from_sys = from_sys;
                modifier;
                name = id}) }

(*------------------------------------------------------------------*)
declaration:
| ldecl=loc(declaration_i)                { ldecl }

declaration_no_concat:
| ldecl=loc(declaration_no_concat_i)      { ldecl }

(*------------------------------------------------------------------*)
declaration_list:
| decl=declaration                        { [decl] }
| decl=declaration_no_concat              { [decl] }
| decl=declaration decls=declaration_list { decl :: decls }

declarations:
| decls=declaration_list TERMINAL { decls }

(*------------------------------------------------------------------*)
/* games */

/* random samplings declarations (global or oracle) */
game_var_rnd:
| RND v=lsymb COLON ty=ty SEMICOLON
    { Crypto.Parse.{ vr_name = v; vr_ty = ty; } } 

game_var_rnds:
| l=slist(game_var_rnd, empty ) { l }

/* variable declaration in an oracle (mutable only) */
game_oracle_var_decl:
| VAR v=lsymb ty=colon_ty? EQ t=term SEMICOLON
    { Crypto.Parse.{ gvd_name = v; gvd_ty = ty; gvd_content = `Mutable t; } } 

game_oracle_var_decls:
| l=slist(game_oracle_var_decl, empty) { l }

/* global variable declaration (mutable or let) */
game_var_decl:
| decl = game_oracle_var_decl    { decl }

| LET v=lsymb ty=colon_ty? EQ t=term SEMICOLON
    { Crypto.Parse.{ gvd_name = v; gvd_ty = ty; gvd_content = `Let t; } } 
| LET v=lsymb ty=colon_ty? EQ SHARPINIT SEMICOLON
    { Crypto.Parse.{ gvd_name = v; gvd_ty = ty; gvd_content = `LetInit; } } 


game_var_decls:
| l=slist(game_var_decl, empty) { l }

/* an update in an oracle */
game_update:
| id=lsymb COLONEQ t=term SEMICOLON { (id,t) }

game_updates:
| l=slist(game_update, empty) { l }

oracle_ret:
| RETURN ret=term SEMICOLON? { ret }

oracle_body:
| rnds=game_var_rnds vars=game_oracle_var_decls updates=game_updates ret=oracle_ret?
{ Crypto.Parse.{ 
    bdy_rnds    = rnds; 
    bdy_lvars   = vars; 
    bdy_updates = updates; 
    bdy_ret     = ret; 
  } 
}

/* an oracle declaration */
oracle_decl:
| ORACLE n=lsymb args=bnds_strict ty=colon_ty? EQ LBRACE body=oracle_body RBRACE
    { Crypto.Parse.{ o_name = n; o_args = args; o_tyout = ty; o_body = body; } }

oracle_decls:
| l=slist(oracle_decl, empty) { l }

game:
| GAME n=lsymb EQ LBRACE
    rnds=game_var_rnds
    vars=game_var_decls
    orcls=oracle_decls 
  RBRACE
    { Crypto.Parse.{ 
        g_name    = n; 
        g_rnds    = rnds; 
        g_gvar    = vars; 
        g_oracles = orcls;
      } 
    }

(*------------------------------------------------------------------*)
tactic_param:
| f=term %prec tac_prec  { TacticsArgs.Term_parsed f }

tactic_params:
| l=slist(tactic_param,COMMA) { l }

(*------------------------------------------------------------------*)
tacargs_string_int:
| s=lsymb                { TacticsArgs.String_name s }
| i=loc(INT)             { TacticsArgs.Int_parsed i }

(*------------------------------------------------------------------*)
%inline rw_mult:
| i=int BANGU { TacticsArgs.Exact i }
| BANGU       { TacticsArgs.Many }
| QMARK       { TacticsArgs.Any }
|             { TacticsArgs.Once }

rw_dir:
|       { `LeftToRight }
| MINUS { `RightToLeft }

rw_type:
| pt=spt                        { `Rw        pt }
| SLASH s=spath_gen             { `Expand    s  }
| SLASH l=lloc(STAR)            { `ExpandAll l  }

expnd_type:
| ATSLASH s=spath_gen      { `Expand    s }
| ATSLASH l=lloc(STAR)     { `ExpandAll l }

rw_item:
| m=rw_mult d=loc(rw_dir) t=rw_type  { TacticsArgs.{ rw_mult = m;
                                                     rw_dir = d;
                                                     rw_type = t; } }

rw_equiv_item:
| d=loc(rw_dir) pt=pt  { TacticsArgs.{ rw_mult = TacticsArgs.Once;
                                         rw_dir = d;
                                         rw_type = `Rw pt; } }

expnd_item:
| d=loc(rw_dir) t=expnd_type  { TacticsArgs.{ rw_mult = TacticsArgs.Once;
                                              rw_dir = d;
                                              rw_type = t; } }


rw_arg:
| r=rw_item { TacticsArgs.R_item r }
| s=s_item  { TacticsArgs.R_s_item s }

rw_args:
| l=slist1(rw_arg, empty) { l }

single_target:
| id=lsymb { id }
| i=loc(int)    { L.mk_loc (L.loc i) (string_of_int (L.unloc i)) }

in_target:
|                                  { `Goal }
| IN l=slist1(single_target,COMMA) { `HypsOrDefs l }
| IN STAR                          { `All }

(*------------------------------------------------------------------*)
fa_arg:
| d=rw_mult t=term %prec tac_prec { (d,t) }

(*------------------------------------------------------------------*)
apply_in:
|             { None }
| IN id=lsymb { Some id }

(*------------------------------------------------------------------*)
deduce_with:
| WITH pt=pt { pt }

(*------------------------------------------------------------------*)
rewrite_oracle_in:
|               { None }
| IN i=loc(INT) { Some i }

(*------------------------------------------------------------------*)
naming_pat:
| UNDERSCORE  { TacticsArgs.Unnamed }
| QMARK       { TacticsArgs.AnyName }
| id=id       { TacticsArgs.Named id }

and_or_ip:
| LBRACKET s=simpl_ip          ips=slist(simpl_ip, empty)    RBRACKET
                    { TacticsArgs.And (s :: ips) }
| LBRACKET s=simpl_ip PARALLEL ips=slist(simpl_ip, PARALLEL) RBRACKET
                    { TacticsArgs.Or  (s :: ips) }
| LBRACKET RBRACKET { TacticsArgs.Split }

rewrite_ip:
| ARROW  { `LeftToRight }
| RARROW { `RightToLeft }

simpl_ip:
| n_ip=naming_pat  { TacticsArgs.SNamed n_ip }
| ao_ip=and_or_ip { TacticsArgs.SAndOr ao_ip }
| d=loc(rewrite_ip) { TacticsArgs.Srewrite d }

s_item_body:
| l=loc(SLASHSLASH)      { TacticsArgs.Tryauto      (L.loc l)}
| l=loc(SLASHEQUAL)      { TacticsArgs.Simplify     (L.loc l)}
| l=loc(SLASHSLASHEQUAL) { TacticsArgs.Tryautosimpl (L.loc l)}

%inline s_item:
| s=s_item_body { s,[] }
| BACKTICK LBRACKET s=s_item_body a=named_args RBRACKET { s, a }

clear_ip:
| LBRACE l=slist1(lsymb, empty) RBRACE { l }

intro_pat:
| l=clear_ip    { TacticsArgs.SClear l }
| s=s_item      { TacticsArgs.SItem (s) }
| l=loc(STAR)   { TacticsArgs.Star  (L.loc l)}
| l=loc(RANGLE) { TacticsArgs.StarV (L.loc l)}
| pat=simpl_ip { TacticsArgs.Simpl pat }
| e=expnd_item  { TacticsArgs.SExpnd e }

intro_pat_list:
| l=slist1(intro_pat,empty) { l }

(*------------------------------------------------------------------*)
int:
|i=INT { i }

selector:
| l=slist1(int,COMMA) { l }

tac_term:
| f=term  %prec tac_prec { f }

as_n_ips:
| AS n_ips=slist1(naming_pat, empty) { n_ips }

%inline sel_tac:
| s=selector COLON r=tac { (s,r) }

sel_tacs:
| l=slist1(sel_tac,PARALLEL) { l }

(*------------------------------------------------------------------*)
pt_arg:
| t=sterm                        { Typing.PTA_term t }
/* Note: some terms parsed as [sterm] may be resolved as [PTA_sub]
   later, using the judgement hypotheses. */

| PERCENT LPAREN pt=pt RPAREN  { Typing.PTA_sub pt }

(*------------------------------------------------------------------*)
/* ambiguous pt */
pt_cnt:
| pt=spt_cnt  { pt }

| head=spt args=slist1(pt_arg,empty)
    { let pta_loc = L.make $startpos $endpos in
      let app = Typing.{ pta_head = head; pta_args = args; pta_loc; } in
      Typing.PT_app app }

pt:
| pt=loc(pt_cnt) { pt }

(*------------------------------------------------------------------*)
/* a symbol optionally applied to some parameters */
applied_symb:
| head=path ty_args=ty_args? se_args=se_args?    { Typing.{ path = head; ty_args; se_args; } }

(*------------------------------------------------------------------*)
/* non-ambiguous pt */

spt_cnt:
| h=applied_symb                { Typing.PT_symb h }
| LOCALIZE LPAREN pt=pt RPAREN  { Typing.PT_localize pt }
| LPAREN pt=pt_cnt RPAREN
    { pt }

spt:
| pt=loc(spt_cnt) { pt }

(*------------------------------------------------------------------*)
/* legacy syntax for use tactic */
pt_use_tac:
| pt=spt { pt }

| head=spt WITH args=slist1(tac_term,COMMA)
    { let pta_loc = L.make $startpos $endpos in
      let args = List.map (fun x -> Typing.PTA_term x) args in
      let app = Typing.{ pta_head = head; pta_args = args; pta_loc; } in
      L.mk_loc pta_loc (Typing.PT_app app) }

(*------------------------------------------------------------------*)
constseq_arg:
| LPAREN b=term RPAREN t=sterm { (b,t) }

(*------------------------------------------------------------------*)
trans_arg_item:
| i=loc(int) COLON t=term %prec tac_prec { i,t }

trans_arg:
| l=lloc(empty)                          { TacticsArgs.TransSystem (L.mk_loc l SE.Parse.NoSystem) }
| LBRACKET annot=system_context RBRACKET { TacticsArgs.TransSystem annot }
| l=slist1(trans_arg_item, COMMA) { TacticsArgs.TransTerms l }

(*------------------------------------------------------------------*)
fresh_arg:
| i=loc(int) { TacticsArgs.FreshInt i }
| l=lsymb    { TacticsArgs.FreshHyp l }

(*------------------------------------------------------------------*)
%inline generalize_dependent:
| GENERALIZE DEPENDENT { }

%inline dependent_induction:
| DEPENDENT INDUCTION { }

%inline rewrite_equiv:
| REWRITE EQUIV { }

%inline rewrite_oracle:
| REWRITE ORACLE { }

(*------------------------------------------------------------------*)
/* local or global formula, un-ambiguous */
/* %inline any_sform: */
/*   |        f=sterm          { Typing.Local f  } /\* default to local formulas *\/ */
/*   | LOCAL  f=sterm          { Typing.Local f  } */
/*   | GLOBAL g=global_formula { Typing.Global g } */

/* local or global formula, ambiguous */
%inline any_form:
  |        f=term           { Typing.Local f  } /* default to local formulas */
  | LOCAL  f=term           { Typing.Local f  }
  | GLOBAL g=global_formula { Typing.Global g }

tac_any_form:
| f=any_form %prec tac_prec { f }

(*------------------------------------------------------------------*)
/* have ip (with AS keyword) for legacy usage (no support for s_items) */
as_have_ip:
| AS ip=simpl_ip { ([],ip,[]) }

have_ip:
| pre=slist(s_item,empty) ip=simpl_ip post=slist(s_item,empty) { (pre, ip, post) }

%inline have_tac:
/* legacy syntax */
| l=lloc(ASSERT) p=tac_term ip=as_have_ip? 
    { mk_abstract l "have" [TacticsArgs.Have (ip, Typing.Local p)] }

/* have ip : any_form */
| l=lloc(HAVE) ip=have_ip COLON p=tac_any_form
    { mk_abstract l "have" [TacticsArgs.Have (Some ip, p)] }

/* have ip : global_form */
| l=lloc(GHAVE) ip=have_ip COLON p=global_formula
    { mk_abstract l "have" [TacticsArgs.Have (Some ip, Typing.Global p)] }

(*------------------------------------------------------------------*)
/* diffie-hellman tactics arguments */

cdh_arg:
| hyp=lsymb COMMA gen=lpath { TacticsArgs.CDH { hyp; gen; } }

gdh_arg:
| hyp=lsymb COMMA gen=lpath { TacticsArgs.GDH { hyp; gen; } }

ddh_arg:
| gen=lpath COMMA na=lpath COMMA nb=lpath COMMA nc=lpath { TacticsArgs.DDH { gen; na; nb; nc; } }

(*------------------------------------------------------------------*)
/* crypto tactic arguments */

crypto_arg_extra:
| COLON bnds=bnds_strict COMMA term=term { bnds, term }

crypto_arg:
| LPAREN glob_sample=lsymb COLON term=term extra=crypto_arg_extra? RPAREN
    { let bnds, cond = Utils.omap_dflt (None,None) (fun (x,y) -> Some x, Some y) extra in
      TacticsArgs.{glob_sample ; term; bnds; cond; } }

(*------------------------------------------------------------------*)
/* Named arguments for tactics */
/* Here we use a "lexical feedback" hack to make it possible to
   parse keywords as lsymbs. The special production [enable_kwd_as_id]
   must be reduced to disable the parsing of keywords as identifiers,
   therefore it cannot be used locally around the [lsymb]s. Thus we
   use it at the level of [named_arg_gen], where it is reduced when
   TILDE is read.
   As a result the genericity of [named_arg_gen] is weakened:
   X can be instantiated by [lsymb] or something like [tacargs_string_int]
   but nothing that includes keywords, such as terms. */

enable_kwd_as_id:
| { Feedback.enable_keywords_as_ids () }
disable_kwd_as_id:
| { Feedback.disable_keywords_as_ids () }

named_arg_gen(X):
| enable_kwd_as_id TILDE l=lsymb disable_kwd_as_id
  { TacticsArgs.NArg l }
| enable_kwd_as_id TILDE l=lsymb COLON
  LBRACKET ll=slist(X,COMMA) RBRACKET
  disable_kwd_as_id
  { TacticsArgs.NList (l,ll) }
| enable_kwd_as_id TILDE l=lsymb COLON a=X disable_kwd_as_id
  { TacticsArgs.NList (l,[a]) }

named_args_gen(X):
| args=slist(named_arg_gen(X),empty) { args }

named_args:
| named_args_gen(lsymb) { $1 }

(*------------------------------------------------------------------*)
tac:
  | LPAREN t=tac RPAREN                { t }
  | l=tac SEMICOLON r=tac              { T.AndThen [l;r] }
  | l=tac SEMICOLON LBRACKET sls=sel_tacs RBRACKET
                                       { T.AndThenSel (l,sls) }
  | l=tac SEMICOLON sl=sel_tac %prec tac_prec
                                       { T.AndThenSel (l,[sl]) }
  | l=lloc(BY) t=tac                   { T.By (t,l) }
  | l=tac PLUS r=tac                   { T.OrElse [l;r] }
  | TRY l=tac                          { T.Try l }
  | REPEAT t=tac                       { T.Repeat t }
  | id=lsymb t=tactic_params           { mk_abstract (L.loc id) (L.unloc id) t }

  (* Special cases for tactics whose names are not parsed as ID
   * because they are reserved. *)

  (* Crypto tactic *)
  | l=lloc(CRYPTO) game=path args=slist(crypto_arg,empty)
    { mk_abstract l "crypto" [TacticsArgs.Crypto (game,args)] }

  | l=lloc(DDH) arg=ddh_arg
    { mk_abstract l "ddh" [TacticsArgs.DH arg] }

  | l=lloc(GDH) arg=gdh_arg
    { mk_abstract l "gdh" [TacticsArgs.DH arg] }

  | l=lloc(CDH) arg=cdh_arg
    { mk_abstract l "cdh" [TacticsArgs.DH arg] }

  (* Case *)
  | l=lloc(CASE) a=named_args t=tac_term
    { mk_abstract l "case" [TacticsArgs.Named_args a; Term_parsed t] }

  (* SMT *)
  | l=lloc(SMT) a=named_args_gen(tacargs_string_int)
    { mk_abstract l "smt" [TacticsArgs.Named_args_gen a] }

  (* Case_Study, equiv tactic, patterns *)
  | l=lloc(CS) t=tac_term
    { mk_abstract l "cs" [TacticsArgs.Term_parsed t] }

  (* Case_Study, equiv tactic, patterns with element number *)
  | l=lloc(CS) t=term IN i=loc(int)
    { mk_abstract l "cs" [TacticsArgs.Term_parsed t; 
                          TacticsArgs.Int_parsed i] }

  (* FA, equiv tactic, patterns *)
  | l=lloc(FA) args=slist1(fa_arg, COMMA)
    { mk_abstract l "fa" [TacticsArgs.Fa args] }

  (* FA, trace tactic *)
  | l=lloc(FA) 
    { mk_abstract l "fa" [] }

  | l=lloc(INTRO) p=intro_pat_list
    { mk_abstract l "intro" [TacticsArgs.IntroPat p] }

  | t=tac l=lloc(DARROW) p=intro_pat_list
    { T.AndThen [t; mk_abstract l "intro" [TacticsArgs.IntroPat p]] }

  | l=lloc(DESTRUCT) i=lsymb
    { mk_abstract l "destruct" [TacticsArgs.String_name i] }

  | l=lloc(DESTRUCT) i=lsymb AS p=and_or_ip
    { mk_abstract l "destruct" [TacticsArgs.String_name i;
                                TacticsArgs.AndOrPat p] }

  | l=lloc(LOCALIZE) i=lsymb AS p=naming_pat
    { mk_abstract l "localize" [TacticsArgs.String_name i;
                                TacticsArgs.NamingPat p] }

  | l=lloc(DEPENDS) args=tactic_params
    { mk_abstract l "depends" args }

  | l=lloc(DEPENDS) args=tactic_params l1=lloc(BY) t=tac
    { T.AndThenSel (mk_abstract l "depends" args, [[1], T.By (t,l1)]) }

  | l=lloc(REMEMBER) t=term AS id=lsymb
    { mk_abstract l "remember" [TacticsArgs.Remember (t, id)] }

  | l=lloc(EXISTS) t=tactic_params
    { mk_abstract l "exists" t }

  | NOSIMPL t=tac                      { T.Modifier ("nosimpl", t) }
  | TIME t=tac  %prec tac_prec         { T.Time t }

  | l=lloc(CYCLE) i=loc(INT)
    { mk_abstract l "cycle" [TacticsArgs.Int_parsed i] }

  | l=lloc(CYCLE) MINUS i=loc(INT)
    { let im = L.mk_loc (L.loc i) (- (L.unloc i)) in
      mk_abstract l "cycle" [TacticsArgs.Int_parsed im] }

  | CHECKFAIL t=tac EXN ts=id  { T.CheckFail (ts, t) }

  | l=lloc(REVERT) ids=slist1(lsymb, empty)
    { let ids = List.map (fun id -> TacticsArgs.String_name id) ids in
      mk_abstract l "revert" ids }

  | l=lloc(GENERALIZE) terms=slist1(sterm, empty) n_ips_o=as_n_ips?
    { mk_abstract l "generalize" [TacticsArgs.Generalize (terms, n_ips_o)] }

  | l=lloc(generalize_dependent) terms=slist1(sterm, empty) n_ips_o=as_n_ips?
    { mk_abstract l "generalize dependent"
                  [TacticsArgs.Generalize (terms, n_ips_o)] }

  | l=lloc(INDUCTION) t=tactic_params
    { mk_abstract l "induction" t}

  | l=lloc(dependent_induction) t=tactic_params
    { mk_abstract l "dependent induction" t }

  | l=lloc(SET) n_ip=naming_pat system=at_X_annot(SYSTEM)? COLONEQ term=term %prec tac_prec
    { mk_abstract l "set" [TacticsArgs.Set (n_ip, system, term)] }

  | l=lloc(CLEAR) ids=slist1(lsymb, empty)
    { let ids = List.map (fun id -> TacticsArgs.String_name id) ids in
      mk_abstract l "clear" ids }

  (*------------------------------------------------------------------*)
  /* assert that we have a formula */
  | t=have_tac { t }

  | t=have_tac l=lloc(BY) t1=tac
    { T.AndThenSel (t, [[1], T.By (t1,l)]) }

  | l=lloc(USE) pt=pt_use_tac ip=as_have_ip?
    { mk_abstract l "have" [TacticsArgs.HavePt (pt, ip, `IntroImpl)] }

  (*------------------------------------------------------------------*)
  /* assert a proof term */
  | l=lloc(HAVE) ip=have_ip? COLONEQ pt=pt 
    { mk_abstract l "have" [TacticsArgs.HavePt (pt, ip, `None)] }

  (*------------------------------------------------------------------*)

  | l=lloc(WEAK) COLONEQ pt=pt i=apply_in
    { mk_abstract l "weak" [TacticsArgs.Weak (Weak_pt pt,i)] }

  | l=lloc(WEAK) t=tac_term i=apply_in
    { mk_abstract l "weak" [TacticsArgs.Weak (Weak_term t,i)] }


  (*------------------------------------------------------------------*)
  | l=lloc(DEDUCE) a=named_args i=slist1(loc(int),COMMA)? w=deduce_with?
    { mk_abstract l "deduce" [TacticsArgs.Deduce (a,i,w)] }

  (*------------------------------------------------------------------*)
  | l=lloc(TRANS) arg=trans_arg
    { mk_abstract l "trans" [TacticsArgs.Trans arg] }

  | l=lloc(FRESH) a=named_args arg=fresh_arg
    { mk_abstract l "fresh" [TacticsArgs.Fresh (a,Some arg)] }

  | l=lloc(FRESH) a=named_args
    { mk_abstract l "fresh" [TacticsArgs.Fresh (a,None)] }

  | l=lloc(AUTO) a=named_args 
    { mk_abstract l "auto" [TacticsArgs.Named_args a] }

  | l=lloc(SIMPL) a=named_args 
    { mk_abstract l "simpl" [TacticsArgs.Named_args a] }

  | l=lloc(REDUCE) a=named_args 
    { mk_abstract l "reduce" [TacticsArgs.Named_args a] }

  | l=lloc(REWRITE) p=rw_args w=in_target
    { mk_abstract l "rewrite" [TacticsArgs.RewriteIn (p, w)] }

  | l=lloc(rewrite_equiv) p=rw_equiv_item
    { mk_abstract l "rewrite equiv" [TacticsArgs.RewriteEquiv (p)] }

  | l=lloc(rewrite_oracle) a=named_args t=sterm pos=rewrite_oracle_in
    { mk_abstract l "rewrite oracle" [TacticsArgs.RewriteOracle (t, a, pos)] }

  | l=lloc(APPLY) a=named_args t=pt w=apply_in
    { mk_abstract l "apply" [TacticsArgs.ApplyIn (a, t, w)] }

  | l=lloc(SPLITSEQ) i=loc(INT) COLON LPAREN ht=term RPAREN dflt=sterm?
    { mk_abstract l "splitseq" [TacticsArgs.SplitSeq (i, ht, dflt)] }

  | l=lloc(CONSTSEQ) i=loc(INT) COLON terms=slist1(constseq_arg, empty)
    { mk_abstract l "constseq" [TacticsArgs.ConstSeq (i, terms)] }

  | l=lloc(MEMSEQ) i=loc(INT) j=loc(INT)
    { mk_abstract l "memseq" [TacticsArgs.MemSeq (i, j)] }

undo:
| UNDO i=INT TERMINAL                 { i }

tactic:
| t=tac TERMINAL                      { t }

biframe:
| ei=term                   { [ei] }
| ei=term COMMA eis=biframe { ei::eis }

/* ----------------------------------------------------------------------- */
%inline quant:
| UFORALL { Typing.PForAll }
| UEXISTS { Typing.PExists }

se_args:
| LBRACE l=slist(s_system_expr,COMMA) RBRACE { l  }

/* ----------------------------------------------------------------------- */
global_formula_i:
| LBRACKET f=term (*t=concrete_term?*) RBRACKET         { Typing.PReach (f,None(*t*)) }
| EQUIV LPAREN e=biframe (*t=concrete_term?*) RPAREN    { Typing.PEquiv (e,None(*t*)) }
| LPAREN f=global_formula_i RPAREN { f }

| f=global_formula ARROW f0=global_formula { Typing.PImpl (f,f0) }

| q=quant vs=bnds_tagged COMMA f=global_formula %prec QUANTIF
                                   { Typing.PQuant (q,vs,f)  }

| f1=global_formula GAND f2=global_formula
                                   { Typing.PAnd (f1, f2) }
| f1=global_formula GOR f2=global_formula
                                   { Typing.POr (f1, f2) }

| LLET v=lsymb ty=colon_ty? EQ t=term IN f=global_formula
    { Typing.PLet (v,t,ty,f) }
  
| DOLLAR LPAREN g=a_global_formula_i RPAREN { g }

(* postfix predicate application *)
| name=upath ty_args=ty_args? se_args=se_args? args=slist(sterm, empty)
    { Typing.PPred Typing.{ name; se_args; ty_args; args; }  }

/* ambiguous global formula, in the sens that it can be confused
   with a local term */
a_global_formula_i:
(* infix predicate application *)
| t=sterm n=infix_s0 ty_args=ty_args? se_args=se_args? t0=sterm 
    { Typing.PPred Typing.{ name = (top_path, n); se_args; ty_args; args = [t; t0]; }  }

/* ----------------------------------------------------------------------- */
/* a_global_formula: */
/* | f=loc(a_global_formula_i) { f } */

global_formula:
| f=loc(global_formula_i) { f }

top_global_formula:
| f=global_formula EOF { f }

/* -----------------------------------------------------------------------
 * Systems
 * ----------------------------------------------------------------------- */

system_item:
| i=tick_uid              { SE.Parse.{ alias = None; system = ([],i); projection = None      } }
| p=path                  { SE.Parse.{ alias = None; system = p;      projection = None      } }
| p=path SLASH proj=lsymb { SE.Parse.{ alias = None; system = p;      projection = Some proj } }

/* ----------------------------------------------------------------------- */
/* a unambiguous system expression (i.e. that does not need to be 
   enclosed in parentheses) */
s_system_expr:
| l=loc(system_item)            /* either a single system item */
    { L.mk_loc (L.loc l) [L.unloc l] }
| LPAREN s=system_expr RPAREN /* or a parenthesized ambiguous system expr */
    { s } 

system_expr:
| s=s_system_expr { s }
/* we unroll one step of the loop, to help menhir see that there 
   are no conflits  */
| h=loc(system_item) COMMA t=loc(slist(system_item,COMMA)) 
    { 
      let loc = L.merge (L.loc h) (L.loc t) in
      L.mk_loc loc (L.unloc h :: L.unloc t)
    }

/* ----------------------------------------------------------------------- */
/* an unambiguous system context (i.e. that does not need to be 
   enclosed in parentheses) */
s_system_context_i:
| l=loc(system_item)            /* either a single system item */
    { SE.Parse.System (L.mk_loc (L.loc l) [L.unloc l]) }
| LPAREN s=system_context_i RPAREN /* or a parenthesized ambiguous context */
    { s } 

s_system_context:
| x=loc(s_system_context_i) { x }

/* a possibly ambiguous system context, that may need to be enclosed in
   parentheses in ambiguous parsing contexts */
system_context_i:
| s=s_system_context_i                
    { s }

/* we unroll one step of the loop, to help menhir see that there 
   are no conflits  */
| h=loc(system_item) COMMA t=loc(slist(system_item,COMMA)) 
    { 
      let loc = L.merge (L.loc h) (L.loc t) in
      SE.Parse.System (L.mk_loc loc (L.unloc h :: L.unloc t))
    }

| SET COLON s=system_expr SEMICOLON
  EQUIV COLON p=system_expr
    { SE.Parse.Set_pair (s,Some p) }

system_context:
| x=loc(system_context_i) { x }

/* ----------------------------------------------------------------------- */
%inline old_system_annot:
| l=lloc(empty)                      { L.mk_loc l SE.Parse.NoSystem }
| LBRACKET s=system_context RBRACKET { s }

at_X_annot(X):
| AT X COLON s=s_system_expr { s }

system_annot:
| AT SYSTEM COLON s=s_system_context { s }
| s=at_X_annot(SET) e=at_X_annot(EQUIV)?
    { 
      let loc = 
        match e with
        | None -> L.loc s
        | Some e -> L.merge (L.loc s) (L.loc e) 
      in
      L.mk_loc loc (SE.Parse.Set_pair (s,e))
    }
| e=at_X_annot(EQUIV) s=at_X_annot(SET)
    { 
      let loc = L.merge (L.loc s) (L.loc e) in      
      L.mk_loc loc (SE.Parse.Set_pair (s,Some e))
    }

/* -----------------------------------------------------------------------
 * Statements and goals
 * ----------------------------------------------------------------------- */

statement_name:
| i=lsymb    { Some i }
| UNDERSCORE { None }

local_statement:
| s=old_system_annot
  name=statement_name
  se_vars=se_bnds
  s2=system_annot?
  ty_vars=ty_vars 
  vars=bnds_tagged
  COLON f=term (*e=concrete_term?*)

  {
    let system = `Local, (Utils.odflt s s2) in
    let formula = Goal.Parsed.Local (f,None (*e*)) in
    Goal.Parsed.{ name; se_vars; ty_vars; vars; system; formula } 
  }

global_statement:
| s=old_system_annot 
  name=statement_name 
  se_vars=se_bnds
  s2=system_annot?
  ty_vars=ty_vars 
  vars=bnds_tagged
  COLON
  f=global_formula

  { 
    let system = `Global, (Utils.odflt s s2) in
    let formula = Goal.Parsed.Global f in
    Goal.Parsed.{ name; se_vars; ty_vars; vars; system; formula } 
  }

obs_equiv_statement:
| s=old_system_annot n=statement_name
  {
    let system = `Global, s in
     Goal.Parsed.{ name = n; system; ty_vars = []; se_vars = []; vars = [];
                   formula = Goal.Parsed.Obs_equiv } 
  }

(*------------------------------------------------------------------*)
lemma_head:
| LEMMA   {}
| THEOREM {}

(*------------------------------------------------------------------*) 
_lemma:
|        lemma_head s=local_statement     { s }
|  LOCAL lemma_head s=local_statement     { s }
| GLOBAL lemma_head s=global_statement    { s }
| EQUIV  s=obs_equiv_statement            { s }
| EQUIV s=old_system_annot name=statement_name vars=bnds_tagged COLON b=loc(biframe) (*t=concrete_term?*)
    { let f = L.mk_loc (L.loc b) (Typing.PEquiv (L.unloc b,None (*t*))) in
      let system = `Global, s in
      Goal.Parsed.{ name; system; ty_vars = []; se_vars = []; vars; formula = Global f } }

lemma:
| x=loc(_lemma) TERMINAL   { x }

(*------------------------------------------------------------------*)
option_param:
| TRUE  { Config.Param_bool true  }
| FALSE { Config.Param_bool false }
| n=id  {
        if n = "true" then (Config.Param_bool true)
        else if n = "false" then (Config.Param_bool false)
        else Config.Param_string n   }
| i=INT { Config.Param_int i      }

set_option:
| SET n=id EQ param=option_param TERMINAL   { (n, param) }

(*------------------------------------------------------------------*)
_hint:
| HINT REWRITE id=path   { Hint.Hint_rewrite id }
| HINT SMT     id=path   { Hint.Hint_smt     id }
| HINT DEDUCE  id=path   { Hint.Hint_deduce  id }

hint:
| x=_hint TERMINAL   { x }

(*------------------------------------------------------------------*)
include_params:
| LBRACKET l=slist(lsymb, COMMA) RBRACKET { l }
|                                         { [] }

(*------------------------------------------------------------------*)
_p_include:
| INCLUDE l=include_params th=quoted_string 
    { ProverLib.{ th_name = ProverLib.Path th; params = l; } }
| INCLUDE l=include_params th=lsymb 
    { ProverLib.{ th_name = ProverLib.Name th; params = l; } }

p_include:
| x=_p_include TERMINAL   { x }

(*------------------------------------------------------------------*)
_query:
| HELP                       { ProverLib.Help }
| PROF                       { ProverLib.Prof }
(* print *)
| PRINT SYSTEM l=system_expr { ProverLib.(Print (Pr_system (Some l))) }

| PRINT l=spath_gen          { ProverLib.(Print (Pr_any l)) }
| PRINT                      { ProverLib.(Print (Pr_system None)) }
(* search *)
| SEARCH t=any_form IN s=system_expr
                              { ProverLib.(Search (Srch_inSys (t,s))) }

| SEARCH t=any_form           { ProverLib.(Search (Srch_term t)) }

query:
| x=_query TERMINAL { x }

(*------------------------------------------------------------------*)
interactive_or_undo:
| u=undo             { ProverLib.Undo u }
| i=interactive      { ProverLib.Input i }

interactive:
| decls=declarations { ProverLib.InputDescr decls }
| set=set_option     { ProverLib.SetOption set }
| h=hint             { ProverLib.Hint h }
| q=query            { q }
| i=p_include        { ProverLib.Include i }
| g=lemma            { ProverLib.Goal g }
| PROOF              { ProverLib.Proof }
| RESET              { ProverLib.Reset }
| EOF                { ProverLib.EOF }

bullet:
| MINUS              { "-" }
| PLUS               { "+" }
| STAR               { "*" }
| s=RIGHTINFIXSYMB   { s }
| s=LEFTINFIXSYMB    { s }

brace:
| LBRACE             { `Open }
| RBRACE             { `Close }

bulleted_tactic:
| bullet bulleted_tactic { (ProverLib.Bullet $1) :: $2 }
| brace  bulleted_tactic { (ProverLib.Brace  $1) :: $2 }
| tactic                 { [ ProverLib.BTactic $1 ] }
| TERMINAL               { [] }

top_proofmode_or_undo:
| u=undo                 { ProverLib.Undo u }
| i=top_proofmode        { ProverLib.Input i }

top_proofmode:
| q=query            { q }
| t=bulleted_tactic  { ProverLib.(Tactic t) }
| ABORT              { ProverLib.Abort }
| QED                { ProverLib.Qed }
| RESET              { ProverLib.Reset }
| EOF                { ProverLib.EOF }
