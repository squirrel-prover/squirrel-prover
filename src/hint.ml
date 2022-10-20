open Utils

module SE = SystemExpr
module L = Location
module Sv = Vars.Sv

type lsymb = Theory.lsymb

type rw_hint = {
  name : string; 
  rule : LowRewrite.rw_rule;
}

let pp_rw_hint fmt rwh : unit =
  Fmt.pf fmt "%s : %a" rwh.name LowRewrite.pp_rw_rule rwh.rule

(*------------------------------------------------------------------*)
module Hm = Term.Hm

type rewrite_db = rw_hint list Hm.t

let pp_rewrite_db fmt (db : rewrite_db) : unit =
  let pp_el fmt (hd, hints) =
    Fmt.pf fmt "@[<v>@[<v 2>%a@;%a@]@]"
      Term.pp_term_head hd
      (Fmt.list pp_rw_hint) hints
  in
  Fmt.pf fmt "@[<v>%a@]" (Fmt.list pp_el) (Hm.bindings db)

let empty_rewrite_db : rewrite_db = Hm.empty

let add_rewrite_rule (h : Term.term_head) (r : rw_hint) db : rewrite_db = 
  let l = odflt [] (Hm.find_opt h db) in
  Hm.add h (r :: l) db

(*------------------------------------------------------------------*)

type hint_db = { db_rewrite : rewrite_db; db_smt : Term.term list }

type Symbols.data += HintDb of hint_db

let default_hint_symb : Symbols.lsymb = L.mk_loc L._dummy "default"
(** Default hint database name.
    For now, this is the only database. *)
                   
(*------------------------------------------------------------------*)
let empty_hint_db = { db_rewrite = empty_rewrite_db; db_smt = [] }

(** Get the hint data-base from the table. 
    Use [default_hint_symb] if there are no hint database yet. *)
let hint_db (table : Symbols.table) : hint_db =
  if not (Symbols.HintDB.mem_lsymb default_hint_symb table) then
    empty_hint_db
  else
    match Symbols.HintDB.data_of_lsymb default_hint_symb table with
    | HintDb db -> db
    | _ -> assert false         (* impossible *)

(** Set the default hint database in the symbol table *)
let set_hint_db (table : Symbols.table) (db : hint_db) : Symbols.table =
  let data = HintDb db in
  match Symbols.HintDB.of_lsymb_opt default_hint_symb table with 
  | None ->
    let table, _ =
      Symbols.HintDB.declare_exact table default_hint_symb () ~data
    in
    table

  | Some default_name ->
    Symbols.HintDB.redefine table default_name ~data ()
      
(*------------------------------------------------------------------*)
let get_rewrite_db table = (hint_db table).db_rewrite
let get_smt_db     table = (hint_db table).db_smt

(*------------------------------------------------------------------*)
type p_hint =
  | Hint_rewrite of lsymb
  | Hint_smt   of lsymb

let add_hint_rewrite (s : lsymb) tyvars form table : Symbols.table =
  let db = hint_db table in
  let pat = Term.pat_of_form form in
  let pat = Term.{ pat with pat_tyvars = tyvars; } in      
  let rule = 
    LowRewrite.pat_to_rw_rule
      ~loc:(L.loc s) ~destr_eq:Term.destr_eq ~destr_not:Term.destr_not 
      SE.any `LeftToRight pat 
  in
  let h = { name = L.unloc s; rule; } in
  let head =
    let src, _ = rule.LowRewrite.rw_rw in
    Term.get_head src
  in
  set_hint_db table
    { db with db_rewrite = add_rewrite_rule head h db.db_rewrite; }

let add_hint_smt formula table : Symbols.table =
  let db = hint_db table in
  set_hint_db table { db with db_smt = formula :: db.db_smt }
