open Squirrelcore
open Utils

module Args = TacticsArgs
module L = Location

module T = ProverTactics

module LT = LowTactics

module St = Term.St
module Sv = Vars.Sv

type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
let dbg = LT.dbg

(*------------------------------------------------------------------*)
let hard_failure = Tactics.hard_failure
let soft_failure = Tactics.soft_failure

(*------------------------------------------------------------------*)
let bad_args = LT.bad_args

(*------------------------------------------------------------------*)
let () =
  T.register_general "case"
    ~pq_sound:true
    (LT.gentac_of_any_tac_arg TraceTactics.case_tac EquivTactics.case_tac)

(*------------------------------------------------------------------*)
let () =
  T.register_general "assumption"
    ~pq_sound:true
    (LT.gentac_of_any_tac_arg
       TraceTactics.assumption_tac
       EquivTactics.assumption_tac)

(*------------------------------------------------------------------*)
let () =
  T.register_general "constraints"
    ~pq_sound:true
    (LT.gentac_of_any_tac_arg
       TraceTactics.constraints_tac
       EquivTactics.constraints_tac)

(*------------------------------------------------------------------*)
let () =
  T.register_general "fa"
    ~pq_sound:true
    (LT.gentac_of_any_tac_arg TraceTactics.fa_tac EquivTactics.fa_tac)

(*------------------------------------------------------------------*)
let () = T.register_general "induction"
    ~pq_sound:true
    (LT.gentac_of_any_tac_arg
       (LT.TraceLT.induction_tac ~dependent:false)
       EquivTactics.old_or_new_induction)

(*------------------------------------------------------------------*)
(* Remark: EquivTactics and TraceTactics implementation of [tac_autosimpl]
   slightly differ, because the [strong] flag is always [true]
   in [TraceTactics.tac_autosimpl] when [Config.auto_intro ()] is [true].
   Because of this asymmetry, there is some code replication below. *)

let tac_autosimpl args s sk fk = 
  let () =
    match args with
    | [] -> ()
    | _ -> hard_failure (Tactics.Failure "no argument allowed")
  in
  match s with
  | Goal.Local s ->
    let sk l fk =
      sk (List.map (fun s -> Goal.Local s) l) fk
    in
    TraceTactics.trace_autosimpl s sk fk
  | Goal.Global _ -> EquivTactics.equiv_autosimpl s sk fk

(*------------------------------------------------------------------*)
(* [auto] and [simpl] *)
let auto : LowTactics.f_simpl =
  fun ~red_param ~strong ~close s sk fk -> 
  match s with
  | Goal.Local s ->
    let sk l fk =
      sk (List.map (fun s -> Goal.Local s) l) fk
    in
    TraceTactics.trace_auto ~red_param ~close ~strong s sk fk
  | Goal.Global _ -> EquivTactics.equiv_auto ~red_param ~close ~strong s sk fk

let tac_auto (args : 'a list) ~(strong:bool) ~(close:bool) : Goal.t Tactics.tac =
  fun s sk fk -> 
  let red_param =
    match args with
    | [] -> Reduction.rp_default
    | [Args.Named_args n] -> Reduction.parse_simpl_args Reduction.rp_default n
    | _ -> bad_args ()
  in
  auto ~red_param ~strong ~close s sk fk

(*------------------------------------------------------------------*)
let () =
  T.register_general "autosimpl"
    ~pq_sound:true
    tac_autosimpl

let () =
  T.register_general "simpl"
    ~pq_sound:true
    (tac_auto ~close:false ~strong:true)

let () =
  T.register_general "auto"
    ~pq_sound:true
    (tac_auto ~close:true ~strong:true)

(*------------------------------------------------------------------*)
let () =
  T.register_general "have"
    ~pq_sound:true
    (LT.have_tac auto)

(*------------------------------------------------------------------*)
let () =
  T.register_general "rewrite"
    ~pq_sound:true
    (LT.rewrite_tac auto)

(*------------------------------------------------------------------*)
let () =
  T.register_general "intro"
    ~pq_sound:true
    (LT.intro_tac auto)
