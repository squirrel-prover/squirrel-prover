(*----------------- History ----------------------------------*)(* {↓{ *)
(** {History Functor}
 * Historiable is the signature of the state that can be saved and
 * restored *)
module type TOPLEVELPROVER = sig
  type state
  val init : unit -> state

  (* TODO This is ugly ! Remove Config from globals ! Or only the
   * params that are ``historiable'' (that can change during
   * computation) *)
  val get_params : state -> Config.params
  val set_params : state -> Config.params -> state
  val get_option_defs : state -> ProverLib.option_def list
  val set_option_defs : state -> ProverLib.option_def list -> state
end

(* This module manage history with global configs *)
module Make (P : TOPLEVELPROVER) = struct
  type state = P.state
  (* could be a tree and managed with ref on current node *)
  type history = state list

  (* should rewrite ocaml module stack ? *)
  type stack = history list

  (* a state of global history is a current history and a stack of
   * history, This could have been clearer with a tree with ref on
   * current node ? FIXME *)
  type history_state = {
    pt_history : history;
    pt_history_stack : stack
  }

  (*---------------------Manage History-----------------------*)(* {↓{ *)
  let init_history : history = []

  let init_history_state : history_state = 
    {pt_history=init_history;pt_history_stack=[]}

  let save_state' (pt_history:history) (st: state) : history =
    let st = P.set_params st (Config.get_params ()) in
    let st = P.set_option_defs st !ProverLib.option_defs in
    st::pt_history

  let save_state (hs:history_state) (st: state) : history_state =
    { hs with pt_history = save_state' hs.pt_history st }

  (* TODO should be deprecated since we do not save in ref…
   * Only Config and options params are to be reset globally here *)
  let reset_from_state (st: state) : state =
    ProverLib.option_defs := P.get_option_defs st;
    let _ = Config.set_params (P.get_params st) in 
    st

  (* Since we still have Config and option params that are global 
   * we have to do the following reset but in the future it will 
   * just return the nth state that will managed by the prover as 
   * his current state *)
  let rec reset_state' (pt_history:history) (n: int) : (
    history * state) =
    if List.length pt_history <= n 
    then init_history, P.init ()
    else match pt_history, n with
    | [], _ -> assert false (* should be managed above *)
    | p::q, 0 -> q, reset_from_state p
    | _::q, n -> (reset_state'[@tailrec]) q (n-1)

  let reset_state (hs:history_state) (n: int) : 
    (history_state * state) =
    let npt_history, nstate  = reset_state' hs.pt_history n in
    ({ hs with pt_history = npt_history }, nstate)

  let reset_to_pt_history_head' (pt_history:history):
  (history * state) =
    reset_state' pt_history 0

  let reset_to_pt_history_head (hs:history_state):
    (history_state * state) =
    reset_state hs 0
  (* }↑} *)
  (*---------------------Manage Stack History-----------------*)(* {↓{ *)
  exception History_stack_empty

  let push_pt_history (hstate:history_state) : history_state =
    { pt_history = []; 
      pt_history_stack = (hstate.pt_history::hstate.pt_history_stack) 
    }

  let pop_pt_history (hstate:history_state) : history_state =
    match hstate.pt_history_stack with 
    | [] -> raise History_stack_empty
    | h::l -> { pt_history = h;
                pt_history_stack = l
              }

  let pop_all_pt_history (hstate:history_state) : history_state =
    match hstate.pt_history_stack with 
    | [] -> raise History_stack_empty (* cannot be empty *)
    | l -> { pt_history = Utils.List.last l;
             pt_history_stack = []
           }
  (* }↑} *)
end
(* }↑} *)
