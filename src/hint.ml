open Utils

module L = Location
module Sv = Vars.Sv

type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
let rev_subst subst = 
  List.map (fun (Term.ESubst (u,v)) -> Term.ESubst (u,v)) subst

(*------------------------------------------------------------------*)

(* FIXME: store and access by head symbol *)
type rewrite_db = (string * Rewrite.rw_erule) list

let empty_rewrite_db = []
let add_rewrite_rule r db = r :: db

let rules = []

(*------------------------------------------------------------------*)

type hint_db = { db_rewrite : rewrite_db; }

let empty_hint_db = { db_rewrite = empty_rewrite_db; }

let get_rewrite_db db = db.db_rewrite

(*------------------------------------------------------------------*)
type p_hint =
  | Hint_rewrite of lsymb

let add_hint_rewrite (s : lsymb) tyvars form db =
  let pat = Match.pat_of_form form in
  let pat = Match.{ pat with pat_tyvars = tyvars; } in      
  let rule = Rewrite.pat_to_rw_erule ~loc:(L.loc s) `LeftToRight pat in
  { db_rewrite = add_rewrite_rule (L.unloc s, rule) db.db_rewrite; }
