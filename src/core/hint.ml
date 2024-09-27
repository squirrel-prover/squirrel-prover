open Utils

module SE = SystemExpr
module L = Location
module Sv = Vars.Sv

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

(** Default hint database name.
    For now, this is the only database. *)
let default_hint_str : string         = "default" 
let default_hint_sp  : Symbols.s_path = [], default_hint_str
let default_hint_p   : Symbols.hintdb = Symbols.HintDB.of_s_path default_hint_sp
                   
(*------------------------------------------------------------------*)
let empty_hint_db = { db_rewrite = empty_rewrite_db; db_smt = [] }

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

(*------------------------------------------------------------------*)
type p_hint =
  | Hint_rewrite of Symbols.p_path
  | Hint_smt     of Symbols.p_path

let add_hint_rewrite (s : Symbols.p_path) tyvars form table : Symbols.table =
  let db = hint_db table in
  let pat = Pattern.pat_of_form form in
  let pat = Term.{ pat with pat_tyvars = tyvars; pat_term = (pat.pat_term,Concrete.LocHyp) } in
  (* TODO:Concrete : placeholder for now but almost sure there is something to do here *)
  let rule = 
    LowRewrite.pat_to_rw_rule
      ~loc:(Symbols.p_path_loc s) ~destr_eq:Term.destr_eq ~destr_not:Term.destr_not 
      SE.full_any GlobalEq `LeftToRight pat 
  in
  let name = Symbols.p_path_to_string ~sep:"_" s in
  let h = { name; rule; } in
  let head =
    let src, _ = rule.LowRewrite.rw_rw in
    Term.get_head src
  in
  set_hint_db table
    { db with db_rewrite = add_rewrite_rule head h db.db_rewrite; }
(* TODO:Concrete : Add the possibility to have concrete rewrite hint *)

let add_hint_smt formula table : Symbols.table =
  let db = hint_db table in
  set_hint_db table { db with db_smt = formula :: db.db_smt }
