open Utils

module L = Location
module Sv = Vars.Sv

type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)

(* FIXME: store and access by head symbol *)
type rewrite_db = (string * Rewrite.rw_erule) list

let empty_rewrite_db = []
let add_rewrite_rule r db = r :: db

(*------------------------------------------------------------------*)

type hint_db = { db_rewrite : rewrite_db; db_smt : Term.message list }

let empty_hint_db = { db_rewrite = empty_rewrite_db; db_smt = [] }

let get_rewrite_db db = db.db_rewrite
let get_smt_db  db = db.db_smt

(*------------------------------------------------------------------*)
type p_hint =
  | Hint_rewrite of lsymb
  | Hint_smt   of lsymb

let add_hint_rewrite (s : lsymb) tyvars form db =
  let pat = Match.pat_of_form form in
  let pat = Match.{ pat with pat_tyvars = tyvars; } in      
  let rule = Rewrite.pat_to_rw_erule ~loc:(L.loc s) `LeftToRight pat in
  { db with db_rewrite = add_rewrite_rule (L.unloc s, rule) db.db_rewrite; }

let add_hint_smt formula db = { db with db_smt = formula :: db.db_smt }
