open Utils
open Ppenv

module SE = SystemExpr
module L = Location
module Sv = Vars.Sv

(*------------------------------------------------------------------*)
(** Parametric type for hints *)
type ('content, 'info) hint = {
  name : string; 
  cnt  : 'content;
  info : 'info;
}

let pp_hint 
    (pp_cnt  : 'a formatter_p)
    (pp_info : 'b formatter_p)
    ppe fmt (h : ('a,'b) hint) : unit 
  =
  Fmt.pf fmt "@[<v 2>%s %a:@,@[%a@]@]" 
    h.name (pp_info ppe) h.info
    (pp_cnt ppe) h.cnt

(*------------------------------------------------------------------*)
(** {3 Rewriting hints } *)

module Hm = Term.Hm

type rw_hint    = (LowRewrite.rw_rule, unit) hint
type rewrite_db = rw_hint list Hm.t

let pp_rw_hint : rw_hint formatter_p =
  pp_hint LowRewrite.pp_rw_rule (fun _ _ _ -> ())

let[@warning "-32"] pp_rewrite_db ppe fmt (db : rewrite_db) : unit =
  let pp_el fmt (hd, hints) =
    Fmt.pf fmt "@[<v>@[<v 2>%a@;%a@]@]"
      Term.pp_term_head hd
      (Fmt.list (pp_rw_hint ppe)) hints
  in
  Fmt.pf fmt "@[<v>%a@]" (Fmt.list pp_el) (Hm.bindings db)

(*------------------------------------------------------------------*)
let empty_rewrite_db : rewrite_db = Hm.empty

let add_rewrite_rule (h : Term.term_head) (r : rw_hint) db : rewrite_db = 
  let l = odflt [] (Hm.find_opt h db) in
  Hm.add h (r :: l) db

(*------------------------------------------------------------------*)
(** {3 Deduction hints } *)

type deduce_info = unit
type deduce_cnt  = { 
  params : Params.t;
  system : SE.context;
  form   : Equiv.form; 
}

type deduce_hint = (deduce_cnt, deduce_info) hint
type deduce_db   = deduce_hint list

let pp_deduce_info _ppe fmt (_i : deduce_info) : unit =
  Fmt.pf fmt ""

let pp_deduce_cnt ppe fmt (c : deduce_cnt) : unit =
  Fmt.pf fmt "%t%a" 
    (fun fmt -> 
       if c.params = Params.empty 
       then Fmt.pf fmt "" 
       else Fmt.pf fmt "[∀ @[%a@]]" Params.pp c.params)
    (Equiv._pp ppe) c.form

let pp_deduce_hint : deduce_hint formatter_p =
  pp_hint pp_deduce_cnt pp_deduce_info

let[@warning "-32"] pp_deduce_db : deduce_db formatter_p =
  fun ppe fmt db ->
  let pp_el fmt hint =
    Fmt.pf fmt "@[%a@]" (pp_deduce_hint ppe) hint
  in
  Fmt.pf fmt "@[<v>%a@]" (Fmt.list pp_el) db

(*------------------------------------------------------------------*)
(** {3 Hint database } *)

type hint_db = { 
  db_rewrite : rewrite_db;
  db_smt     : Term.term list;
  db_deduce  : deduce_db;
}

type Symbols.data += HintDb of hint_db

(*------------------------------------------------------------------*)
(** Default hint database name.
    For now, this is the only database. *)
let default_hint_str : string         = "default" 
let default_hint_sp  : Symbols.s_path = [], default_hint_str
let default_hint_p   : Symbols.hintdb = Symbols.HintDB.of_s_path default_hint_sp
                   
(*------------------------------------------------------------------*)
let empty_hint_db = { 
  db_rewrite = empty_rewrite_db; 
  db_smt     = []; 
  db_deduce  = []; 
}

(** Get the hint data-base from the table. 
    Use [default_hint_symb] if there are no hint database yet. *)
let hint_db (table : Symbols.table) : hint_db =
  if not (Symbols.HintDB.mem_sp default_hint_sp table) then
    empty_hint_db
  else
    match Symbols.HintDB.get_data default_hint_p table with
    | HintDb db -> db
    | _ -> assert false         (* impossible *)

(** Set the default hint database in the symbol table *)
let set_hint_db (table : Symbols.table) (db : hint_db) : Symbols.table =
  let data = HintDb db in
  if Symbols.HintDB.mem_sp default_hint_sp table then
    Symbols.HintDB.redefine table default_hint_p ~data
  else
    let table, _ =
      Symbols.HintDB.declare
        ~approx:false table ~scope:Symbols.top_npath
        (L.mk_loc L._dummy default_hint_str) ~data
    in
    table
      
(*------------------------------------------------------------------*)
let get_rewrite_db table = (hint_db table).db_rewrite
let get_smt_db     table = (hint_db table).db_smt
let get_deduce_db  table = (hint_db table).db_deduce

(*------------------------------------------------------------------*)
(** {3 Adding hints } *)

(** Surface AST to add hints. *)
type p_hint =
  | Hint_rewrite of Symbols.p_path
  | Hint_smt     of Symbols.p_path
  | Hint_deduce  of Symbols.p_path

(*------------------------------------------------------------------*)
let add_hint_rewrite (s : Symbols.p_path) pat_params system form table : Symbols.table =
  let db = hint_db table in
  let pat = Pattern.pat_of_form form in
  let pat = Term.{ pat with pat_params; pat_term = (pat.pat_term,Concrete.LocHyp) } in
  let rule = 
    LowRewrite.pat_to_rw_rule
      ~loc:(Symbols.p_path_loc s) ~destr_eq:Term.destr_eq ~destr_not:Term.destr_not 
      system GlobalEq `LeftToRight pat 
  in
  let name = Symbols.p_path_to_string ~sep:"_" s in
  let h = { name; cnt = rule; info = (); } in
  let head =
    let src, _ = rule.LowRewrite.rw_rw in
    Term.get_head src
  in
  set_hint_db table
    { db with db_rewrite = add_rewrite_rule head h db.db_rewrite; }

(*------------------------------------------------------------------*)
let add_hint_smt formula table : Symbols.table =
  let db = hint_db table in
  set_hint_db table { db with db_smt = formula :: db.db_smt }

(*------------------------------------------------------------------*)
let add_hint_deduce (s : Symbols.p_path) params system form table : Symbols.table =
  let db = hint_db table in
  let name = Symbols.p_path_to_string ~sep:"_" s in
  let h = { name; cnt = { params; system; form;}; info = (); } in
  set_hint_db table { db with db_deduce = h :: db.db_deduce; }
