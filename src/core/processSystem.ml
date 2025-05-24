open Utils
open Process

module L  = Location
module Sv = Vars.Sv
module Mv = Vars.Mv
module SE = SystemExpr

type lsymb = Symbols.lsymb
type subst = Term.subst

(*------------------------------------------------------------------*)
(** We use dummy locations for intermediary term we build, which do not come
    from the user. *)
let mk_dummy (v : 'a) : 'a L.located = L.mk_loc L._dummy v

(*------------------------------------------------------------------*)
(** {2 Tagged process} *)

(** Supplementary information used to translate a process into a system. *)
type info = {
  id : int ;      (** unique identifier *)
  alias : string  (** current alias *)
}

(** Not exported.
    Before translating a process into a system of actions,
    we use an intermediary type to represent our system.
    Compared to the type Process.proc, [tproc] does not feature
    some constructs (e.g. New, Apply, Alias) and adds an information
    field to each (sub)process. *)
type tproc =
  | TNull     of info
  | TIn       of info * Symbols.channel * Vars.var * tproc
  | TOut      of info * Symbols.channel * Term.term * tproc
  | TParallel of info * tproc * tproc
  | TSet      of info * Multicell.t * Term.term * tproc
  | TLet      of info * Vars.var * Term.term * Type.ty * tproc
  | TRepl     of info * Vars.var * tproc
  | TExists   of info * Vars.vars * Term.term * tproc * tproc
  | TLock     of info * Mutex.Multi.t * tproc
  | TUnlock   of info * Mutex.Multi.t * tproc

(** Get the info associated to a process. *)
let get_info = function
  | TNull info
  | TIn (info, _, _, _)
  | TOut (info, _, _, _)
  | TParallel (info, _, _)
  | TSet (info, _, _, _)
  | TLet (info, _, _, _, _)
  | TRepl (info, _, _)
  | TExists (info, _, _, _, _)
  | TLock (info, _, _)
  | TUnlock (info, _, _) -> info

let get_id (tproc : tproc) = (get_info tproc).id

let get_alias (tproc : tproc) = (get_info tproc).alias

(** Fold a function over all subprocesses. *)
let rec fold f proc acc =
  let acc = f proc acc in
  match proc with
    (* Arity 0 *)
    | TNull _ -> acc
    (* Arity 1 *)
    | TIn (_, _, _, p)
    | TOut (_, _, _, p)
    | TSet (_, _, _, p)
    | TLet (_, _, _, _, p)
    | TRepl (_, _, p)
    | TLock (_, _, p)
    | TUnlock (_, _, p) -> fold f p acc
    (* Arity 2 *)
    | TParallel (_, p1, p2)
    | TExists (_, _, _, p1, p2) -> fold f p2 (fold f p1 acc)

let is_try_find = function
  | TExists (_,[],_,_,_) -> false
  | TExists (_,_,_,_,_) -> true
  | _ -> false

(*------------------------------------------------------------------*)
(** {2 Declarations} *)
(*------------------------------------------------------------------*)
(** Functions to create lemmas and axioms associated to a process
    declaration*)

(** [register_name n_var ty indices table] register in [table] a name [n]
    corresponding to the variable [x]'s name with the type [ty].
    Also register in the table the corresponding namelength axioms.
    Returns the updated table and the term [n] applied to [indices].*)
let register_name n_var ty indices table =
  let n_fty = Type.mk_ftype_tuple [] (List.map Vars.ty indices) ty in
  (* declare a new name symbol *)
  let table, nsymb =
    let n_lsymb = mk_dummy (Vars.name n_var) in
    let data = Symbols.Name { n_fty } in
    (* location not useful, declaration cannot fail *)
    Symbols.Name.declare ~approx:true table n_lsymb ~data
  in

  (* add name length axioms *)
  let table = Lemma.add_namelength_axiom table nsymb n_fty in
  let n_term =
    let nsymb = Term.nsymb nsymb ty in
    Term.mk_name_with_tuple_args nsymb (Term.mk_vars indices)
  in
  n_term, table

(*------------------------------------------------------------------*)
(** {2 Alias} *)

type alias_name =
  | UserName of string (** user-provided name *)
  | Hint     of string (** naming hint, e.g. obtained from a process name *)
  | Empty

let string_of_alias_name = function
  | Empty -> "A"
  | UserName s | Hint s -> s

let apply_new_hint (s : string) (alias : alias_name) =
  match alias with
  | UserName _ -> alias
  | Hint _ | Empty -> Hint s

(*------------------------------------------------------------------*)
(** {2 Pre-process} *)
(** The pre-processing phase translate a [Process.proc] into a [tproc].
    This translation removes New, Alias and Apply nodes.
    Add [info] to each node with a unique [id].
    Also, names (and their lemma) are declared for each New instruction. *)

(** Environment for the pre-processing. *)
type preproc_env = {

  subst : subst ;
  (** Substitution to apply as part of pre-processing. *)

  indices : Vars.var list ;
  (** Current indices. Names created by New will be parameterized by these. *)

  alias : alias_name ;
  (** Current alias. *)

  dollar_alias : string option;
  (** String to be used to replace $ in aliases.
      It will be the closest user-provided alias that does
      not itself start with a $. *)

  projs : Projection.t list
  (** Projections of the system.
      Have to be checked when a sub-process is called by Apply. *)
}

(** Initial environement *)
let init_preproc_env (projs : Projection.t list) : preproc_env = {
  subst = [] ;
  indices = [] ;
  alias = Empty ;
  dollar_alias = None ;
  projs = projs ;
}

(** Translate a [Process.proc] into a [tproc]:
    - Inline [Apply] constructs, keeping aliases unless one was
      present above in the initial process.
    - Remove [New] constructs by introducing new names. *)
let preprocess
      (proc : proc)
      (projs : Projection.t list)
      (time : Vars.var)
      table
    : tproc * Symbols.table =

  (* Counter used to generate unique identifiers. *)
  let counter = ref 0 in

  (* Recursive pre-processing function, returning tproc and
     the table enriched with names added by [New] instructions. *)
  let rec aux (proc : proc) table (penv : preproc_env) :
      tproc * Symbols.table =
    let info =
      let alias = string_of_alias_name penv.alias in
      let alias =
        match penv.dollar_alias with
        | None -> alias
        | Some top -> String.concat top (String.split_on_char '$' alias)
      in
      { id = !counter ; alias }
    in
    incr counter;
    (* To be called when no tproc node is generated. *)
    let unused_info () = decr counter in
    match proc with
    | New (x, ty, p) ->
      unused_info ();
      (* We add a new name to the table, with its axioms.
         Then we recurse with a substitution mapping [x] to [n_term],
         i.e. the name applied to its indices. *)
      let n_term, table = register_name x ty (List.rev penv.indices) table in
      let penv =
        { penv with subst = Term.ESubst (Term.mk_var x, n_term) :: penv.subst }
      in
      aux p table penv

    | Apply (symb, args) ->
      unused_info ();
      (* Get from [table] the process associated to [symb]. *)
      let pdecl = get_process_data table symb in
      (* Check projections. *)
      if penv.projs <> pdecl.projs then
        error (ProjsMismatch (penv.projs, pdecl.projs));
      (* Add substitutions from declaration variables to the arguments in
         the current substitution.
         Also subtitute the process' time variable for the system's. *)
      let args = List.map (Term.subst penv.subst) args in
      let vars = List.map Term.mk_var pdecl.args in
      let new_subst =
        List.map2 (fun var arg -> Term.ESubst (var, arg)) vars args
      in
      let subst = List.append new_subst penv.subst in
      let subst =
        (Term.ESubst (Term.mk_var pdecl.time, Term.mk_var time)) :: subst
      in
      (* Update the alias name. *)
      let alias = apply_new_hint (Symbols.to_string symb.s) penv.alias in
      (* Recursion on the process found in the table. *)
      aux pdecl.proc table { penv with subst; alias }

    | Alias (p, name) ->
      unused_info ();
      let dollar_alias =
        assert (name <> "");
        if name.[0] = '$' then penv.dollar_alias else Some name
      in
      aux p table { penv with alias = UserName name ; dollar_alias }

    | Repl (i, p) ->
      (* We add [i] to the environment's indices *)
      let penv = { penv with indices = i :: penv.indices } in
      let tproc, table = aux p table penv in
      TRepl (info, i, tproc), table

    | Exists (i, t, p1, p2) ->
      (* We add the list [i] to the environment's indices *)
      let penv1 = { penv with indices = i @ penv.indices } in
      let tproc1, table = aux p1 table penv1 in
      let tproc2, table = aux p2 table penv in
      let t = Term.subst penv.subst t in
      TExists (info, i, t, tproc1, tproc2), table

    (* Other case are simple recursions *)
    | Null ->
      TNull info, table
    | In (c, x, p) ->
      let tproc, table = aux p table penv in
      TIn (info, c, x, tproc), table
    | Out (c, t, p) ->
      let tproc, table = aux p table penv in
      let t = Term.subst penv.subst t in
      TOut (info, c, t, tproc), table
    | Parallel (p1, p2) ->
      let tproc1, table = aux p1 table penv in
      let tproc2, table = aux p2 table penv in
      TParallel (info, tproc1, tproc2), table
    | Set (mcell, t, p) ->
      let tproc, table = aux p table penv in
      let mcell = Multicell.map (Term.subst penv.subst) mcell in
      let t = Term.subst penv.subst t in
      TSet (info, mcell, t, tproc), table
    | Let (x, t, ty, p) ->
      let tproc, table = aux p table penv in
      let t = Term.subst penv.subst t in
      TLet (info, x, t, ty, tproc), table
    | Lock (m, p) | Unlock (m, p) as cur_p ->
      let m =
        Mutex.Multi.map
          (fun v ->
             match Term.subst penv.subst (Term.mk_var v) with
             | Var v' -> v'
             | _ -> assert false)
          m
      in
      let tproc, table = aux p table penv in
      begin match cur_p with
      | Lock _ -> TLock (info, m, tproc), table
      | _      -> TUnlock (info, m, tproc), table
      end
  in
  aux proc table (init_preproc_env projs)

(*------------------------------------------------------------------*)
(** {2 Automaton} *)
(** This section defines a finite automaton and its alphabet.
    It is used to determine at which point in the process we have to
    register an action. *)

(* In the theory, label kinds are simply called labels.
   The star label is used for let, skip, event and write.
   Reads may happen with most labels.

   In our [label_kind] type the two labels for conditionals are merged into a
   single one, and we omit labels for parallel composition and replication.
   We also separate writes because they are the only ones that may
   cause WR conflicts. Note that our conflict analysis initially determines
   whether an update is in WR conflict or not (i.e. its write is in conflict,
   and not only its implicit reads) but this information is currently not
   reported. *)
type label_kind =
  | LIn | LOut
  | LCond
  | LUpdate
  | LStar
  | LLock | LUnlock

type label = {
  conflict : bool ;
  kind : label_kind
}

let string_of_label_kind = function
  | LIn -> "in"
  | LOut -> "out"
  | LCond -> "cond"
  | LUpdate -> "update"
  | LLock -> "lock"
  | LUnlock -> "unlock"
  | LStar -> "star"

let pp_label fmt lbl =
  Format.fprintf fmt "%s%s"
    (string_of_label_kind lbl.kind)
    (if lbl.conflict then "(conflict)" else "")

(** State for s-block automaton. *)
type s_state = Forward | Backward

(** Transitions for s-block automaton. *)
let s_transition = function
  | Forward, {kind=LLock}
  | Forward, {kind=LCond;conflict=false}
  | Forward, {kind=LIn;conflict=false}
  | Forward, {kind=LUpdate;conflict=false}
  | Forward, {kind=LStar;conflict=false} -> Some Forward
  | Forward, _ -> Some Backward
  | Backward, {kind=LUnlock}
  | Backward, {kind=LCond;conflict=false}
  | Backward, {kind=LOut;conflict=false}
  | Backward, {kind=LUpdate;conflict=false}
  | Backward, {kind=LStar;conflict=false} -> Some Backward
  | _ -> None

(** State for c-block automaton. *)
type c_state = Retractable | Transparent | Forcable

let c_transition = function
  | Retractable, {kind=LUpdate;conflict=false}
  | Retractable, {kind=LIn}
  | Retractable, {kind=LLock}
  | Retractable, {kind=LStar} -> Some Retractable
  | (Retractable|Transparent), {kind=LCond} -> Some Transparent
  | (Retractable|Transparent), _ -> Some Forcable
  | Forcable, {kind=LIn;conflict=false}
  | Forcable, {kind=LUnlock;conflict=false}
  | Forcable, {kind=LOut|LStar|LUpdate} -> Some Forcable
  | _ -> None

(** Extra automaton for imposing Squirrel-specific constraints. *)

type x_state = { has_input : bool ; has_output : bool }

let x_transition = function
  | {has_input=false} as s, {kind=LIn} -> Some { s with has_input = true }
  | {has_output=false} as s, {kind=LOut} -> Some { s with has_output = true }
  | _,{kind=LIn|LOut} -> None
  | s,_ -> Some s

(** Final automaton: product of c, s and x automata. *)

type state = s_state * c_state * x_state

let initial_state = Forward, Retractable, {has_input=false;has_output=false}

(** Describe the transition of the finite automaton.
    Warning : a transition must exist from the initial state
    for any label, i.e. [transition initial_state label]
    must be different from [None] for any [label].*)
let transition ((s,c,x):state) (label : label) : state option =
  match
    s_transition (s, label),
    c_transition (c, label),
    x_transition (x, label)
  with
  | Some s', Some c', Some x' -> Some (s',c',x')
  | _ -> None

(** [next_state state label] returns [(false,state')] when [state']
    is the next state in the block automaton. If undefined we return
    [true,state'] where [state'] is the result of reading [label]
    from the initial state -- it will be part of a new block. *)
let next_state (state : state) (label : label) : bool * state option =
  match transition state label with
  | Some new_state -> false, Some new_state
  | None ->
      true,
      match transition initial_state label with
      | Some s -> Some s
      | None ->
          Format.printf "Cannot handle %a!@." pp_label label ;
          assert false

(*------------------------------------------------------------------*)
(** {2 Tagging each part of the process } *)

module Sint = Set.Make(Int)
module Mint = Map.Make(Int)

(** [find_cuts proc labels] returns the set of identifiers
    of subprocesses of [proc] where we have to register an action
    before processing the rest of the process.
    The map [labels] associates to each subprocess its label to
    be used for the block automaton given by [next_state]. *)
let find_cuts (proc : tproc) (labels : label Mint.t) : Sint.t =
  (* State becomes None after we encounter a subprocess without label,
     e.g. a parallel composition, in which case we always cut.
     This prevents cutting twice when parallel compositions are nested. *)
  let rec aux proc (state : state option) (result : Sint.t) : Sint.t =
    let id = get_id proc in
    let cut,state =
      match state, Mint.find_opt id labels with
      | Some state, Some label -> next_state state label
      | Some _, None -> true, None
      | None, Some label -> next_state initial_state label
      | None, None -> false, None
    in
    let result = if cut then Sint.add id result else result in
    match proc with
    | TNull _ -> result
    | TIn (_, _, _, p)
    | TOut (_, _, _, p)
    | TSet (_, _, _, p)
    | TLet (_, _, _, _, p)
    | TRepl (_, _, p)
    | TLock (_, _, p)
    | TUnlock (_, _, p) -> aux p state result
    | TParallel (_, p1, p2)
    | TExists (_, _, _, p1, p2) -> aux p2 state (aux p1 state result)
  in
  aux proc None Sint.empty

(** David: move this in Action module? *)
let get_choice_ints (action : Action.action_v) : int * int =
  match action with
  | [] -> assert false
  | { par_choice = p_int, _; sum_choice = s_int, _ } :: _ ->
    p_int, s_int

let add_new_item (action : Action.action_v) : Action.action_v =
  { par_choice = 0, []; sum_choice = 0, [] } :: action

let add_repl (action : Action.action_v) (i : Vars.var) : Action.action_v =
  match action with
  | [] -> assert false
  | { par_choice = p_int, p_vars; sum_choice } :: action2 ->
    (* Sanity check, a replication cannot be added after a condition
       in the same item. *)
    assert (sum_choice = (0, []));
    { par_choice = p_int, p_vars@[i]; sum_choice } :: action2

let add_try_find (action : Action.action_v) (vars : Vars.vars) : Action.action_v =
  match action with
  | [] -> assert false
  | { par_choice; sum_choice = s_int, s_vars } :: action2 ->
    { par_choice; sum_choice = s_int, vars @ s_vars } :: action2

let modify_par_choice_int (action : Action.action_v) (n : int) : Action.action_v =
  match action with
  | [] -> assert false
  | { par_choice = _, p_vars; sum_choice } :: action2 ->
    { par_choice = n, p_vars; sum_choice } :: action2

let modify_sum_choice_int (action : Action.action_v) (n : int) : Action.action_v =
  match action with
  | [] -> assert false
  | { par_choice; sum_choice = _, s_vars } :: action2 ->
    { par_choice; sum_choice = n, s_vars } :: action2

(** [name_cuts proc cuts] maps each identifier in [cuts] to an action.
    The action is determined by the process structure (parallel compositions
    and choices). *)
let name_cuts (proc : tproc) (cuts : Sint.t) : Action.action_v Mint.t =
  (* [aux proc (action, result)] traverses [proc].
     If an action has to be generated for a subprocess,
     we add a mapping from its identifier to [action] in the result.
     Also return and the [par_choice] and
     [sum_choice] to be applied after [proc]. *)
  let rec aux
            proc
            ((action, result) : Action.action_v * Action.action_v Mint.t)
          : int * int * Action.action_v Mint.t =
    let id = get_id proc in
    let p_int, s_int = get_choice_ints action in
    let cut = Sint.mem id cuts in
    let result = if cut then Mint.add id (List.rev action) result else result in
    let action = if cut then add_new_item action else action in
    match proc with
    | TNull _ ->
      if cut then
        (p_int+1, s_int+1, result)
      else
        (p_int, s_int, result)
    | TIn (_, _, _, p)
    | TOut (_, _, _, p)
    | TSet (_, _, _, p)
    | TLet (_, _, _, _, p)
    | TLock (_, _, p)
    | TUnlock (_, _, p) ->
      let p_int0, s_int0, result0 = aux p (action, result) in
      if cut then
        p_int+1, s_int+1, result0
      else
        p_int0, s_int0, result0
    | TRepl (_, i, p) ->
      let p_int0, s_int0, result0 = aux p (add_repl action i, result) in
      if cut then
        p_int+1, s_int+1, result0
      else
        p_int0, s_int0, result0
    | TParallel (_, p1, p2) ->
      let p_int1, _, result1 = aux p1 (action, result) in
      let action2 = modify_par_choice_int action p_int1 in
      let p_int2, _, result2 = aux p2 (action2, result1) in
      if cut then
        (p_int+1, s_int+1, result2)
      else
        (p_int2, 0, result2)
    | TExists (_, vars, _, p1, p2) ->
      let action1 = add_try_find action vars in
      let p_int1, s_int1, result1 = aux p1 (action1, result) in
      let action2 = modify_sum_choice_int action s_int1 in
      let p_int2, s_int2, result2 = aux p2 (action2, result1) in
      assert (p_int1 = p_int2);
      if cut then
        p_int+1, s_int+1, result2
      else
        p_int2, s_int2, result2
  in
  let _, _, result = aux proc (add_new_item [], Mint.empty) in
  result

(** The type [current_action] describes, at a given point in the process,
    what will be the action generated:
    - [action]: describe the name of the action, or its strict prefix.
    - [strict]: [`Strict] if [action] is a prefix (i.e. there are branching
      before the next cut), [`Large] otherwise.
    This object is used to define global macros.
    Note that if an action is generated at an identifier of the process, this
    object describes the next one. *)
type future_action = {
  action : Action.action_v ;
  strict : [`Large | `Strict] }

(** [make_strict future_action] changes [future_action] into corresponding
    strict one if it is not already strict. *)
let make_strict (future_action : future_action) : future_action =
  match future_action.strict with
  | `Large ->
    { action = List.rev (List.tl (List.rev future_action.action)) ;
      strict = `Strict }
  | `Strict -> future_action

(** [make_future_actions proc names] return a maps from some identifier in
    [proc] to an object of type [future_action].
    The results only maps identifiers of [TLet] sub-process. *)
let make_future_actions (proc : tproc) (names : Action.action_v Mint.t) :
    future_action Mint.t =
  (* [aux proc result] traverses [proc] and return then accumulator [acc]
     and a [future_action] if one is generated in [proc].*)
  let rec aux proc (acc : future_action Mint.t)
      : future_action Mint.t * (future_action option) =
    let id = get_id proc in
    let current_action = Option.map
      (fun action -> { action ; strict = `Large })
      (Mint.find_opt id names)
    in
    match proc with
    | TNull _ ->
      acc, current_action
    | TLet (_, _, _, _, p) ->
      let acc, future_action = aux p acc in
      let acc = Mint.add id (Option.get future_action) acc in
      let action = match current_action with
        | Some _ -> current_action
        | None -> future_action
      in
      acc, action
    | TRepl (_, _, p)
    | TIn (_, _, _, p)
    | TOut (_, _, _, p)
    | TSet (_, _, _, p)
    | TLock (_, _, p)
    | TUnlock (_, _, p) ->
      let acc, future_action = aux p acc in
      let action = match current_action with
        | Some _ -> current_action
        | None -> future_action
      in
      acc, action
    | TParallel (_, p1, p2)
    | TExists (_, _, _, p1, p2) ->
      let acc1, future_action1 = aux p1 acc in
      let acc2, future_action2 = aux p2 acc1 in
      let future_action : future_action option =
        match future_action1, future_action2 with
          | None, None -> None
          | Some a1, None ->
            let sa1 = make_strict a1 in
            Some sa1
          | None, Some a2 ->
            let sa2 = make_strict a2 in
            Some sa2
          | Some a1, Some a2 ->
            let sa1 = make_strict a1 in
            let sa2 = make_strict a2 in
            assert (sa1 = sa2); (* sanity check *)
            Some sa1
      in
      let action = match current_action with
        | Some _ -> current_action
        | None -> future_action
      in
      acc2, action
  in
  let result, _ = aux proc Mint.empty in
  result

(*------------------------------------------------------------------*)
(** {2 Pretty-printing} *)

(** Format a tproc with one subprocess per line,
    showing identifiers. *)
let pp_tproc (cuts:Sint.t option) fmt (proc:tproc) : unit =
  let rec print proc =
    let id = get_id proc in
    let print_branch name =
      Format.fprintf fmt " %2d - %s@." (get_id proc) name
    in
    Format.fprintf fmt "%c%2d - "
      (match proc,cuts with
       | _, None -> ' '
       | TNull _, Some _ -> ' ' (* id+1 not meaningful *)
       | _, Some set when Sint.mem (id+1) set -> '*'
       | _ -> ' ')
      (get_id proc);
    match proc with
    | TNull _ ->
      Format.fprintf fmt "null@."
    | TIn (_,c,x,p) ->
      Format.fprintf fmt "in(%a,%a)@." Channel.pp c Vars.pp x;
      print p
    | TOut (_,c,t,p) ->
      Format.fprintf fmt "out(%a,%a)@." Channel.pp c Term.pp t;
      print p
    | TParallel (_,p1,p2) ->
      Format.fprintf fmt "parallel/left@.";
      print p1;
      print_branch "parallel/right";
      print p2
    | TSet (_,multicell,t,p) ->
      Format.fprintf fmt "@[<hov 2>%a :=@ %a@]@."
        Multicell.pp multicell
        Term.pp t;
      print p
    | TLet (_,x,t,_,p) ->
      Format.fprintf fmt "let %a = %a@." Vars.pp x Term.pp t;
      print p
    | TRepl (_,x,p) ->
      Format.fprintf fmt "!_%a@." Vars.pp x;
      print p
    | TExists (_,[],cond,p1,p2) ->
      Format.fprintf fmt "if %a@." Term.pp cond;
      print p1;
      print_branch "else";
      print p2
    | TExists (_,vars,cond,p1,p2) ->
      Format.fprintf fmt
        "try find %a such that %a@."
        Vars.pp_list vars
        Term.pp cond;
      print p1;
      print_branch "else";
      print p2
    | TLock (_,m,p) ->
      Format.fprintf fmt "lock %a@." Mutex.Multi.pp m;
      print p
    | TUnlock (_,m,p) ->
      Format.fprintf fmt "unlock %a@." Mutex.Multi.pp m;
      print p
  in print proc

let pp_tproc_with_cuts cuts fmt tproc = pp_tproc (Some cuts) fmt tproc

let pp_tproc fmt tproc = pp_tproc None fmt tproc

(*------------------------------------------------------------------*)
(** {2 Conflicts} *)

(** We are interested in write/write and read/write conflicts.
    Write operations are clearly indicated as [TSet] subprocesses,
    while read operations are implicit in [TOut], [TSet], [TLet] and
    [TExists].

    We have a conflict between two such operations if one is a write
    and they can be executed concurrently: this requires that they
    belong to parallel subprocesses, or the same replicated subprocess,
    and they are not protected by a common lock.

    More precisely, each operation is associated to an indexed cell,
    and and set of indexed locks. We determine symbolically if two
    actions may act on the same cell without having any lock in common,
    over-approximating real conflicts.
    The [conflict] functions computes read and write operations for
    all subprocesses, and for each parallel composition or replication,
    detects conflicts arising at that point. *)

exception Invalid_lock_usage of int*tproc (* process ID, process *)
exception Invalid_indices    of int*tproc (* process ID, process *)
exception Cannot_cut         of int*tproc

let () =
  Errors.register (function
    | Invalid_lock_usage (i,tproc) ->
        Some { printer =
          fun _ fmt ->
            Format.fprintf fmt
                "Invalid lock usage at subprocess #%d:@.@.%a"
                i
                pp_tproc tproc }
    | Invalid_indices (i,tproc) ->
        Some { printer =
          fun _ fmt ->
            Format.fprintf fmt
                "Indices must be replication-bound at subprocess #%d:@.@.%a"
                i
                pp_tproc tproc }
    | Cannot_cut (i,tproc) ->
        Some { printer =
          fun _ fmt ->
            Format.fprintf fmt
                "Cannot cut on try-find at subprocess #%d:@.@.%a"
                i
                pp_tproc tproc }
    | _ -> None)

(** TODO ajouter tests pour Invalid_lock_usage *)

(** Given a [tproc], return the set of locks owned at each point,
    as a hash table from process identifiers to multimutexes:
    the multimutexes associated to a subprocess are those owned *before*
    the subprocess is executed.

    This may fail if the process makes certain uses of locks, which
    we consider bad practice. Note that the notion of well-locked
    from the theory is not enough to guarantee success here.

    This function also checks that locks are used as in the process
    calculus from the paper, i.e. they are indexed by variables
    bound in replications. *)
let locks projs (top_p:tproc) : int -> Mutex.Multi.t list =
  let locks = Hashtbl.create 256 in
  (* The theory does not require that cell indices are bound by replications
     but we enforce it in case non-trivial multicells are present (i.e., a
     multicell actually featuring a diff) for the soundness of conflict
     analysis (which relies on formulas that mix indices coming from various
     projections). *)
  let non_trivial_multicell = ref false in
  let bad_index_multicell = ref None in
  (* Rough conditions allowing to conclude that inclusion holds
     (at the level of addresses): either there is no diff in mutexes,
     or mutexes on one side are indexed by all replication indices,
     in order -- in that case, mutexes on this side are said to be
     unique. *)
  let non_trivial_multimutex = ref false in
  let unique_mutexes = ref (List.map (fun p -> p,true) projs) in
  let update_mutex_conditions (m:Mutex.Multi.t) repl_vars =
    non_trivial_multimutex :=
      !non_trivial_multimutex ||
      List.exists (fun (_,x) -> x <> snd (List.hd m)) m;
    unique_mutexes :=
      List.map
        (fun (p,b) -> p, b && (List.assoc p m).args = repl_vars)
        !unique_mutexes
  in
  let rec aux repl_vars current p =
    Hashtbl.add locks (get_id p) current ;
    let invalid_lock_usage () = raise (Invalid_lock_usage (get_id p, top_p)) in
    let invalid_indices () = raise (Invalid_indices (get_id p, top_p)) in
    match p with
    (* Cases with operations on mutexes *)
    | TLock (_,m,p) ->
        (* Lock indices must be bound by replications. *)
        if not @@
           List.for_all
             (fun (_,{Mutex.args}) ->
                List.for_all (fun v -> List.mem v repl_vars) args)
             m
        then
          invalid_indices ();
        (* Double locking is invalid. *)
        if List.mem m current then invalid_lock_usage ();
        update_mutex_conditions m (List.rev repl_vars);
        aux repl_vars (m::current) p
    | TUnlock (_,m,p) ->
        (* Can only unlock a statically owned lock. *)
        if not (List.mem m current) then invalid_lock_usage ();
        update_mutex_conditions m (List.rev repl_vars);
        aux repl_vars (List.filter ((<>) m) current) p
    | TSet (_,c,_,p) ->
        if
          Multicell.fold
            (fun b -> function
               | Term.Var v -> b || not (List.mem v repl_vars)
               | _ -> true)
            false
            c
        then
          bad_index_multicell := Some (get_id p, top_p);
        if not (List.for_all ((=) (List.hd c)) c) then
          non_trivial_multicell := true;
        aux repl_vars current p
    (* Locks cannot be carried accross parallel compositions. *)
    | TRepl _ | TParallel _ | TNull _ when current <> [] ->
        invalid_lock_usage ()
    | TRepl (_,v,p) -> aux (v::repl_vars) [] p
    | TParallel (_,p,q) -> aux repl_vars [] p ; aux repl_vars [] q
    (* Transparent cases with 0, 1 or 2 subprocesses. *)
    | TNull _ -> ()
    | TIn (_,_,_,p)
    | TOut (_,_,_,p)
    | TLet (_,_,_,_,p) -> aux repl_vars current p
    | TExists (_,_,_,p,q) -> aux repl_vars current p ; aux repl_vars current q
  in
  aux [] [] top_p;
  begin match !non_trivial_multicell, !bad_index_multicell with
  | true, Some (i,p) -> raise (Invalid_indices (i,p))
  | _ -> ()
  end;
  if !non_trivial_multimutex then begin
    let good_projs =
      List.filter_map
        (fun (p,b) -> if b then Some p else None)
        !unique_mutexes
    in
    if good_projs = [] then
      Printer.prt `Warning
        "This system cannot be used to prove \
         diff-inclusions or diff-equivalences."
    else
      Printer.prt `Warning
        "This system can only be used to prove diff-inclusions \
         x ⊆ y@ for y ∈ @[%a@]."
        (Utils.pp_list Projection.pp)
        good_projs
  end else
    Printer.prt `Warning
      "System can be used to prove diff-equivalences \
       and diff-inclusions.";
  fun i -> Hashtbl.find locks i

(** Given a [tproc], compute the sets of bound variables for all
    subprocesses. Note that the bound variables associated e.g. to
    a replication do not include the index variable bound in that
    replication. *)
let bound_variables (p:tproc) : int -> Vars.vars =
  let vars = Hashtbl.create 256 in
  let rec aux current p =
    Hashtbl.add vars (get_id p) current ;
    match p with
    (* Cases with binders *)
    | TIn (_,_,var,p)
    | TLet (_,var,_,_,p)
    | TRepl (_,var,p) -> aux (var::current) p
    | TExists (_,vars,_,p,q) -> aux (vars@current) p; aux current q
    (* Transparent cases with 0, 1 or 2 subprocesses. *)
    | TNull _ -> ()
    | TLock (_,_,p)
    | TUnlock (_,_,p)
    | TOut (_,_,_,p)
    | TSet (_,_,_,p) -> aux current p
    | TParallel (_,p,q) -> aux current p ; aux current q
  in
  aux [] p ;
  fun i -> Hashtbl.find vars i

type vsubst = (Vars.var*Vars.var) list

let rec refresh (v:Vars.var) (vars:Vars.vars) : Vars.vars*vsubst =
  match vars with
  | [] -> assert false
  | v'::vars ->
      let v'' = Vars.refresh v' in
      let vars,subst =
        if v = v' then vars,[] else refresh v vars
      in
      v''::vars, (v',v'')::subst

(* Determine if two accesses may create a conflict, over-approximating.
   Each access comes with its (multi)cell and currently owned (multi)locks
   as well as bound variables (the same for all projections).
   We also have the bound variables [vars] common to both conflicts,
   used for a sanity check.

   We discuss below the general approach, for single processes,
   then how multiprocesses are handled.

   **General approach**

   In the simple case where all variables are bound above a parallel
   composition, we will check for the validity of a formula
   [cells_equal => locks_intersect] where [cells_equal] expresses that
   the operations access the same memory cell and [locks_intersect]
   expresses that the sets of lock owned by the two operations
   intersect. This formula is implicitly universally quantified over the
   bound variables [vars] common to both accesses and bound variables
   specific to each operation. It is crucial that the latter two sets
   of variables are disjoint, which we check in an assertion, and should
   always be the case given how we create processes (there is a sanity
   check on that point in the code).

   For instance, without the de Bruijn convention,
   (!_i lock l(i) ; s(j) := ...) | (!_i lock l(i) ; s(i) := ...)
   would yield the valid formula j = i => i = i whereas a conflict
   should be detected. With
   (!_i lock l(i) ; s(j) := ...) | (!_i' lock l(i') ; s(i') := ...)
   we generate j = i => i = i' which is not valid, detecting
   the conflict.

   When dealing with a replication [TRepl (_,i,p)] we need to similarly
   consider operations arising from [p] and from a copy of [p] where
   [i] is renamed into a fresh variable [j], under the assumption that
   [i] and [j] are distinct.

   Consider for instance a process of the following form:

   !_j !_i (<aquire some locks depending on i,j> ; s(i,j) := ...)

   At the level of the !_i we have no conflicting write:
   parallel sessions will have different values for it.
   The generated formula is of the form i <> i' => (i,j) = (i',j) => ...
   which is trivially valid. Note that we have refreshed i but not
   j which is bound above the branching point !_i.

   At the level of the !_j however we cannot assume that the two
   values for i are the same: we refresh both j and i, obtaining the
   formula j <> j' => (i,j) = (i',j') => ...
   which may result in a conflict depending on the acquired locks.

   In a way, we implicitly expanded the process into
   (!_i ...; s(i,j) := ...) | (!_i s(i,j') := ...) and then refreshed
   it into (!_i ...; s(i,j) := ...) | (!_i' s(i',j') := ...)
   to ensure de-Bruijn's convention again. This operation is actually
   not performed on processes but directly on their sets of operations.

   ** Dealing with multiprocesses **

   The [locks_intersect] formula must express that operations have a lock in
   common *on all projections where the conflict occurs*. This list of
   projections is given as the [projs] argument of the function.
   This is what the theory currently requires,
   although it would probably be sound to rule out a conflict when
   there is a lock in common *on some projection*
   because our analyses are on multi-traces. *)
let conflict
      table projs vars ?rename
      (vars1,(locks1:Mutex.Multi.t list),(cell1:Cell.t))
      (vars2,(locks2:Mutex.Multi.t list),(cell2:Cell.t))
    : bool =
  (* Rename second operation if needed. *)
  let refresh_neq,vars2,locks2,cell2 =
    match rename with
    | None -> Term.mk_true,vars2,locks2,cell2
    | Some v ->
        let vars2,vsubst = refresh v vars2 in
        let subst =
          List.map
            (fun (x,y) -> Term.ESubst (Term.mk_var x, Term.mk_var y))
            vsubst
        in
        Term.(mk_neq (mk_var v) (mk_var (List.assoc v vsubst))),
        vars2,
        List.map
          (Mutex.Multi.map
             (fun x -> try List.assoc x vsubst with Not_found -> x))
          locks2,
        (fst cell2, List.map (Term.subst subst) (snd cell2))
  in
  (* Check de Bruijn convention. *)
  let sanity varsX varsY =
    List.for_all
      (fun v -> List.mem v vars || rename = Some v || not (List.mem v varsY))
      varsX
  in
  assert (sanity vars1 vars2);
  assert (sanity vars2 vars1);
  let cells_equal =
    if fst cell1 <> fst cell2 then
      Term.mk_false
    else
      Term.mk_eqs (snd cell1) (snd cell2)
  in
  let locks_equal (lock1:Mutex.t) (lock2:Mutex.t) =
    if lock1.symb <> lock2.symb then
      Term.mk_false
    else
      Term.mk_eqs
        (List.map Term.mk_var lock1.args)
        (List.map Term.mk_var lock2.args)
  in
  (* Formula requiring that locks intersect (between the two accesses)
     on a given projection. *)
  let locks_intersect_on proj =
    let locks1 = List.map (List.assoc proj) locks1 in
    let locks2 = List.map (List.assoc proj) locks2 in
    List.fold_left
      (fun f lock1 ->
        List.fold_left
          (fun f lock2 ->
             Term.mk_or f (locks_equal lock1 lock2))
          f
          locks2)
      Term.mk_false
      locks1
  in
  (* Formula requiring that locks intersection on all [projs]. *)
  let locks_intersect =
    List.fold_left
      (fun f proj -> Term.mk_and f (locks_intersect_on proj))
      Term.mk_true
      projs
  in
  let formula =
    Term.mk_impl refresh_neq
      (Term.mk_impl cells_equal locks_intersect)
  in
  not (Constr.is_tautology ~timeout:1 ~table formula)

(** Memory accesses are given by a memory cell and, optionally,
    a projection. When projection is [Some p] it means that the
    access occurs on projection [p], otherwise it may occur in
    all projections. *)
type access = Projection.t option * Cell.t

(* Maps from process IDs to sets of accesses represented as lists. *)
module Accesses = struct
  module ASet =
    Set.Make(struct type t = access let compare = Stdlib.compare end)
  type t = ASet.t Mint.t
  let empty = Mint.empty
  let add i a map =
    Mint.update i
      (function
         | None -> Some (ASet.singleton a)
         | Some s -> Some (ASet.add a s))
      map
  let iter (f : int -> access -> unit) map =
    Mint.iter
      (fun i s -> ASet.iter (fun a -> f i a) s)
      map
  let disjoint _ _ _ = assert false
  let union s1 s2 =
    Mint.union disjoint s1 s2
end

(** Operations on [Term.projection option] used as in type [access]. *)
module Projopt = struct
  (** Return true if two projections may be equal. *)
  let may_eq p1 p2 = match p1,p2 with
    | Some p1, Some p2 -> p1 = p2
    | _ -> true
  let _pp fmt = function
    | None -> Format.fprintf fmt "*"
    | Some p -> Projection.pp fmt p
end

(** Analyze [p] and return a map of conflicts:
    to each subprocess identifier [i] we associate the identifiers
    of subprocesses in conflict -- this is a multiple association
    table. *)
let conflicts
      table
      projs
      (bound_variables : int -> Vars.vars)
      (locks : int -> Mutex.Multi.t list)
      p
    : (int,int) Hashtbl.t =
  let conflicts = Hashtbl.create 256 in
  (* Detect conflicts from two sets of accesses.
     The first set corresponds to write operations, which is useful
     only for more informative error messages.
     Write-write conflicts are symmetric: no need to call
     [detect w1 w2] and [detect w2 w1].
     A variable can be passed as rename in which case it will be refreshed
     in the right hand-side conflict data, with the assumption that the
     fresh variable is distinct from the original: this is useful for
     replication. *)
  let detect ?rename vars (s1:Accesses.t) (s2:Accesses.t) =
    Accesses.iter
      (fun i (proj_i,cell_i) ->
         Accesses.iter
           (fun j (proj_j,cell_j) ->
              let locks_i = locks i in
              let locks_j = locks j in
              let vars_i = bound_variables i in
              let vars_j = bound_variables j in
              let data_i = vars_i,locks_i,cell_i in
              let data_j = vars_j,locks_j,cell_j in
              let projs =
                match proj_i,proj_j with
                | Some p, Some _ ->
                    (* We will only check for conflicts if proj_i = proj_j,
                       and in that case we only need locks protecting
                       the conflict for this single projection. *)
                    [p]
                | None,_ | _,None ->
                    (* In all other cases we have to consider that
                       the accesses may occur on any projection,
                       thus we will check that locks prevent conflicts
                       on all projections. *)
                    projs
              in
              if Projopt.may_eq proj_i proj_j &&
                 conflict ?rename table projs vars data_i data_j
              then begin
                (* The conflict may have already been added for other
                   projections or accesses. *)
                if List.mem j (Hashtbl.find_all conflicts i) then
                  assert (List.mem i (Hashtbl.find_all conflicts j))
                else begin
                  Hashtbl.add conflicts i j;
                  if j <> i then Hashtbl.add conflicts j i
                end
              end)
           s2)
      s1
  in
  (* Add to [rs] all read accesses from [t], tracking projections. *)
  let rec add_reads ?proj id t (rs:Accesses.t) =
    match t with
    | Term.Macro (m,indices,_) ->
      let rs =
        begin match Symbols.get_macro_data m.s_symb table with
        | Symbols.State _ -> Accesses.add id (proj,(m.s_symb,indices)) rs
        | _ -> rs
        end
      in
      Term.tfold (fun tm rs -> add_reads ?proj id tm rs) t rs
    | Term.(Diff (Explicit args)) ->
      assert (proj = None);
      List.fold_left
        (fun rs (proj,tm) -> add_reads ~proj id tm rs)
        rs
        args
    | _ ->
      Term.tfold (fun tm rs -> add_reads ?proj id tm rs) t rs
  in
  let add_reads id (l:Term.t list) (rs:Accesses.t) =
    List.fold_left (fun rs t -> add_reads id t rs) rs l
  in
  let rec process : tproc -> Accesses.t * Accesses.t = function
    (* Cases where conflicts are detected. *)
    | TParallel ({id=i},p,q) ->
        let reads_p,writes_p = process p in
        let reads_q,writes_q = process q in
        let vars = bound_variables i in
        detect vars writes_p reads_q;
        detect vars writes_p writes_q;
        detect vars writes_q reads_p;
        Accesses.union reads_p reads_q,
        Accesses.union writes_p writes_q
    | TRepl ({id},i,p) ->
        let reads,writes = process p in
        detect ~rename:i (bound_variables id) writes writes;
        detect ~rename:i (bound_variables id) writes reads;
        reads,writes
    (* Cases where read/write operations are added. *)
    | TSet ({id=i},multicell,t,p) ->
        let rs,ws = process p in
        let indices =
          Multicell.fold
            (fun indices i -> i::indices)
            []
            multicell
        in
        let rs = add_reads i (t::indices) rs in
        let ws =
          List.fold_left2
            (fun ws proj cell -> Accesses.add i (Some proj,cell) ws)
            ws
            projs
            multicell
        in
        rs,ws
    | TOut ({id=i},_,t,p)
    | TLet ({id=i},_,t,_,p) ->
        let rs,ws = process p in
        let rs = add_reads i [t] rs in
        rs,ws
    | TExists ({id},_,cond,p,q) ->
        let rs,ws = process p in
        let rs',ws' = process q in
        let rs = Accesses.union rs rs' in
        let ws = Accesses.union ws ws' in
        let rs = add_reads id [cond] rs in
        rs,ws
    (* Transparent cases *)
    | TNull _ -> Accesses.empty,Accesses.empty
    | TIn (_,_,_,p)
    | TLock (_,_,p) (* lock indices cannot contain reads *)
    | TUnlock (_,_,p) -> process p
  in
  ignore (process p);
  conflicts

(** [make_labels conflict proc] returns a mapping from each identifiers
    in [proc] to an element of type [label].
    It takes a [conflict] predicate indicating which subprocesses (given
    by their ID) may trigger conflicts.  *)
let make_labels
      (conflict:int->bool)
      (proc : tproc)
    : label Mint.t =
  fold
    (fun p map ->
       try
         let kind = match p with
           | TParallel _ | TRepl _ | TNull _ -> raise Not_found
           | TIn _ -> LIn
           | TOut _ -> LOut
           | TExists _ -> LCond
           | TSet _ -> LUpdate
           | TLet _ -> LStar
           | TLock _ -> LLock
           | TUnlock _ -> LUnlock
         in
         let label =
           { conflict = conflict (get_id p) ; kind }
         in
         if label = { kind = LCond ; conflict = true } &&
            is_try_find p
         then
           raise (Cannot_cut (get_id p, p));
         Mint.add (get_id p) label map
       with Not_found -> map)
    proc
    Mint.empty

(*------------------------------------------------------------------*)
(** {2 Translation environment} *)

(** Data stored while translating a process into a set of actions. *)
type p_env = {
  (* CONSTANT VALUES *)
  system_name : System.t;
  (** name of the system being processed *)
  projs : Projection.t list;
  (** valid projections for the process being parsed *)
  time : Vars.var;
  (** term variable representing the current time-point *)
  dummy_in : Vars.var;
  (** term variable used for actions without input *)
  exec_model : Action.exec_model;
  (** Classic or PQ models *)
  input_macro : Term.msymb;

  (* PROPAGATED BETWEEN ACTIONS *)
  table : Symbols.table ;
  (** current state of the table *)
  alias : string ;
  (** current alias used for action names in the process *)
  indices : Vars.var list ;
  (** current list of bound indices (coming from Repl or Exists constructs) *)
  subst : Term.esubst list ;
  (** substitution built along the way *)
  inputs : (Channel.t * Vars.var) list ;
  (** bound input variables *)

  (* RELATED TO THE CURRENT ACTION *)
  input : Channel.t * Vars.var ;
  (** current action's input *)
  evars : Vars.var list ;
  (** variables bound by existential quantification *)
  facts : Term.term list ;
  (** list of formulas to create the condition term of the action *)
  updates : (Symbols.macro * Term.terms * Term.term) list ;
  (** List of updates performed in the action of the form [(s, args, body)].
      See [updates] in [Action.descr] for a description of the semantics. *)
  globals : Symbols.macro list;
  (** list of global macros declared in [action] *)
  output : Symbols.channel * Term.term
}

(** Initial environment *)
let init_penv system_name projs time exec_model table : p_env =
  let dummy_in = Vars.make_fresh Type.tmessage "$dummy" in
  let input_macro =
    match exec_model with
    | Action.Classic -> Macros.Classic.inp
    | Action.PostQuantum -> Macros.Quantum.inp
  in
  { system_name;
    projs;
    time;
    dummy_in;
    exec_model;
    input_macro;

    table;
    alias = "A" ;
    indices = [] ;
    subst = [] ;
    inputs = [] ;

    input = Symbols.dummy_channel, dummy_in ;
    evars = [] ;
    facts = [] ;
    updates = [] ;
    globals = [] ;
    output = Symbols.dummy_channel, Term.empty ;
  }

(** Reset the environment after the declaration of an action *)
let reset_penv penv : p_env =
  { penv with
    input = Symbols.dummy_channel, penv.dummy_in ;
    evars = [] ;
    facts = [] ;
    updates = [] ;
    globals = [] ;
    output = Symbols.dummy_channel, Term.empty ;
  }

(*------------------------------------------------------------------*)
(** {2 State macro handling} *)

(** [subst_macros_ts table l ts t] returns [t] where state macro occurrences
    of the form [s@ts] are replaced by [s@pred(ts)] if [s] is NOT in [l]. *)
let subst_macros_ts table l ts t =
  let rec doit (t : Term.term) : Term.term =
    match t with
    | Macro (symb, terms, (Var ts' as vts)) when ts' = ts ->
      let terms = List.map doit terms in
      begin match Symbols.get_macro_data symb.s_symb table with
      | Symbols.State _ when not (List.mem symb.s_symb l) ->
        Term.mk_macro symb terms (Term.mk_pred vts)
      | _ ->
        Term.mk_macro symb terms vts
      end
    | _ -> Term.tmap doit t
  in
  doit t

(** [normalize_term t penv] applies [penv.subst] to [t] and
    replaces each macro [s@tau] by [s@(pred tau)] if
    [s] is not updated in [penv]. *)
let normalize_term (t : Term.term) penv =
  let t' = Term.subst penv.subst t in
  let updated_states = List.map (fun (s,_,_) -> s) penv.updates in
  subst_macros_ts penv.table updated_states penv.time t'

(*------------------------------------------------------------------*)
(** {2 Declarations } *)

(** Registers a global macro in [penv.table].
    Return the updated [penv], the chosen macro symbol [s],
    and the term `s(penv.indices)@penv.time` which will be used in
    the translation to represent the let-defined variable. *)
let register_globals
    (penv : p_env)
    (name : string)
    (body : Term.term)
    (ty : Type.ty)
    (shape : Action.shape)
    (suffix : [`Strict | `Large])
    : p_env * Symbols.macro * Term.term =

  let body = normalize_term body penv in

  let indices = List.rev penv.indices in

  let inputs =
    if fst penv.input = Symbols.dummy_channel then
      penv.inputs
    else
      penv.input :: penv.inputs
  in
  let invars = List.map snd inputs in

  let table, symb =
    Macros.declare_global
      penv.table
      penv.system_name
      penv.exec_model
      (L.mk_loc L._dummy name)
      ~suffix
      ~action:shape
      ~inputs:invars
      ~indices:indices
      ~ts:penv.time
      body
      ty
  in
  assert (not (TConfig.strict_let_mode penv.table &&
               name <> Symbols.to_string symb.s));

  (* Term to which the let-bound variable will translate. *)
  let args = Term.mk_vars (List.rev penv.indices) in
  let glob_term =
    Term.mk_macro (Macros.msymb table symb) args (Term.mk_var penv.time) in

  { penv with table }, symb, glob_term

(** Registers an action [penv.table] according to [penv].
    Returns [penv] properly modified for the rest of the translation. *)
let register_action (penv : p_env) action : p_env =

  (* In strict alias mode, we require that the alias T is available. *)
  let exact = TConfig.strict_alias_mode penv.table in

  let table, name =
    (* To have an informative location here would require keeping
       locations as part of tprocs. *)
    let loc = odflt L._dummy None in
    Action.fresh_symbol penv.table ~exact (L.mk_loc loc penv.alias)
  in

  let in_ch, in_var = penv.input in
  let indices = List.rev penv.indices in
  let action_term = Term.mk_action name (Term.mk_vars indices) in
  let in_tm = Term.mk_macro penv.input_macro [] action_term in

  (* We will use [register_action] to register an action.
     To obtain the terms for the new action we will use a substitution
     [subst]. However, [register_action] may decide to use a different
     symbol for the action. It will take care itself of renaming the
     components of the registered action, but we have to keep track of
     this for the rest of the translation: this is done by computing
     a [new_subst] after the registration. *)

  let subst_interm =
    [Term.ESubst (Term.mk_var penv.time, action_term);
     Term.ESubst (Term.mk_var in_var, in_tm)]
  in
  let subst =
    subst_interm @
    List.map
      Term.(function ESubst (t1, t2) -> ESubst (t1, subst subst_interm t2))
      penv.subst
  in

  (* Compute the condition, updates and output of this action. *)
  let condition =
    let vars = List.rev penv.evars in
    let t = Term.subst subst (Term.mk_ands penv.facts) in
    (vars,t)
  in
  let updates =
    List.map
      (fun (ms,args,t) ->
        (ms,
         List.map (Term.subst subst) args,
         Term.subst subst t))
      penv.updates
  in
  let output : Symbols.channel * Term.term =
    let (c,t) = penv.output in
    c, Term.subst subst t
  in

  let action_descr = Action.{
    name; action;
    exec_model = penv.exec_model;
    input   = in_ch;
    indices = indices;
    globals = penv.globals;
    condition; updates; output }
  in

  Action.check_descr action_descr;

  let table, new_name, _ =
    System.register_action table penv.system_name action_descr
  in

  let table =
    if new_name <> name then Symbols.Action.remove name table else table
  in

  let new_action_term =
    Term.mk_action new_name (Term.mk_vars action_descr.indices)
  in
  let new_in_tm = Term.mk_macro penv.input_macro [] new_action_term in

  let new_subst =
    let open Term in
    (ESubst (mk_var in_var, new_in_tm)) ::
    (List.map
       (function ESubst(t1, t2) ->
          ESubst(t1,
            subst
              [ESubst (mk_var penv.time, new_action_term);
               ESubst (mk_var in_var, new_in_tm)]
              t2))
      penv.subst)
  in
  reset_penv { penv with
               table ;
               subst = new_subst ;
               inputs = penv.input :: penv.inputs }

(*------------------------------------------------------------------*)
(** {2 Processing } *)

let process_system_decl
    _proc_loc (p : tproc) (penv : p_env)
    (actions_name : Action.action_v Mint.t)
    (future_actions : future_action Mint.t)
  : Symbols.table =

  let rec aux (p : tproc) penv : Symbols.table =
    let id = get_id p in
    (* Generate action if [actions_name] contains an action for [id]. *)
    let action_opt = Mint.find_opt id actions_name in
    let penv =
      Option.fold
        ~none:penv ~some:(register_action penv) action_opt
    in
    let penv = { penv with alias = get_alias p } in
    match p with
    | TNull _ -> penv.table

    | TIn (_,c,x,p) ->
      aux p { penv with input = (c,x) }

    | TOut (_,c,t,p) ->
      aux p { penv with output = (c,normalize_term t penv) }

    | TParallel (_,p1,p2) ->
      let table1 = aux p1 penv in
      aux p2 { penv with table = table1 }

    | TSet (_,multicell,t,p) ->
      let add_update s l t penv =
        if List.exists (fun (s',_,_) -> s = s') penv.updates then
          (* Not supported by current translation. *)
          error (DuplicatedUpdate (Symbols.path_to_string s));
        let t' = normalize_term t penv in
        let l' = List.map (Term.subst penv.subst) l in
        { penv with
          updates = (s,l',t') :: penv.updates }
      in
      let penv =
        match multicell with
        | (s,l) as cell :: tl when List.for_all ((=) cell) tl ->
          (* All updates on same cell: add_update with given term. *)
          add_update s l t penv
        | _ ->
          (* Otherwise we add_update projection by projection,
             which means that all cells will have to be distinct.
             The update multiterm for a projection coincides with [t]
             on that projection and is [s@pred τ] on others. *)
          let default s args =
            Term.mk_macro
              (Macros.msymb penv.table s)
              args
              (Term.mk_var penv.time)
          in
          List.fold_left2
            (fun penv proj (s,l) ->
               let t =
                 Term.mk_diff
                   (List.map
                      (fun proj' ->
                         proj',
                         if proj' = proj then
                           Term.project1 proj t
                         else
                           default s l)
                      penv.projs)
               in
               add_update s l t penv)
            penv
            penv.projs
            multicell
      in
      aux p penv

    | TLet (_,x,t,ty,p) ->
      (* Sanity check: type is correct + type is fully inferred. *)
      assert (Type.equal (Term.ty t) ty && not (Type.contains_tuni ty));

      let future_action = Mint.find id future_actions in
      let shape = Action.get_shape_v  future_action.action in
      let penv, symb, glob_term =
        register_globals
          penv (Vars.name x) t ty shape future_action.strict
      in

      let penv0 =
        { penv with
          subst = Term.ESubst (Term.mk_var x, glob_term) :: penv.subst;
          globals = symb :: penv.globals }
      in
      aux p penv0

    | TRepl (_,i,p) ->
      let penv0 = { penv with indices = i :: penv.indices } in
      aux p penv0

    | TExists (_,evars,cond,p1,p2) ->
      let fact = normalize_term cond penv in
      let facts_p1 = fact :: penv.facts in
      let facts_p2 =
        match evars with
        | [] -> (Term.mk_not fact) :: penv.facts
        | qvars ->
          Term.mk_forall ~simpl:false qvars (Term.mk_not fact) :: penv.facts
      in

      let penv1 =
        { penv with
          indices = List.rev_append evars penv.indices ;
          evars   = List.rev_append evars penv.evars ;
          facts = facts_p1 }
      in
      let table1 = aux p1 penv1 in
      let penv2 =
        { penv with
          table = table1;
          facts = facts_p2 }
      in
      let table2 = aux p2 penv2 in
      table2

    | TLock (_,_,p)
    | TUnlock (_,_,p) -> aux p penv

  in
  aux p penv

(*------------------------------------------------------------------*)
(** Collect the set of actions appearing in a process without pending
    applications. *)
let collect_actions (p : tproc) =
  let rec doit acc : tproc -> _ = function
    | TNull _ -> acc
    | TIn (_,_,_,p)
    | TRepl (_,_,p)
    | TLock (_,_,p)
    | TUnlock (_,_,p) -> doit acc p
    | TLet (_,_,t,_,p)
    | TOut (_,_,t,p) -> doit (doit_term acc t) p
    | TSet (_,l,t,p) ->
        let acc = Multicell.fold doit_term acc l in
        doit (doit_term acc t) p
    | TParallel (_,p1,p2) -> doit (doit acc p1) p2
    | TExists (_,_,t,p1,p2) -> doit (doit (doit_term acc t) p1) p2

  and doit_term acc : Term.term -> _ = function
    | Term.Action (a,_) -> if not (List.mem a acc) then a :: acc else acc
    | _ as t -> Term.tfold ((^~) doit_term) t acc

  in
  doit [] p

(** Check that the system only uses defined actions
    (i.e. any action declared using `action A : i` has been
    defined in the system). *)
let check_actions_all_def table (p : tproc) =
  let actions = collect_actions p in
  List.iter (fun a ->
      if not (Action.is_def a table) then
        error (ActionUndef a)
    ) actions

(*------------------------------------------------------------------*)
(** {2 System declaration } *)

(* FIXME: fix user-defined projections miss-used *)
let system_conflicts
    (table : Symbols.table)
    (projs : Projection.t list) (proc : Parse.t)
  : (int,int) Hashtbl.t
  =
  (* Type-check the process. *)
  let time, p =
    let pdecl = parse table ~args:[] projs proc in
    assert (projs = pdecl.projs && pdecl.args = []);
    pdecl.time, pdecl.proc
  in
  let tproc, _ = preprocess p projs time table in
  let bound_variables = bound_variables tproc in
  let locks = locks projs tproc in
  conflicts table projs bound_variables locks tproc

(* FIXME: fix user-defined projections miss-used *)
let declare_system
    (table : Symbols.table) (exec_model : Action.exec_model)
    (system_name : lsymb option)
    (projs : Projection.t list) (proc : Parse.t)
  : Symbols.table
  =
  (* Type-check the process. *)
  let time, p =
    let pdecl = parse table ~args:[] projs proc in
    assert (projs = pdecl.projs && pdecl.args = []);
    pdecl.time, pdecl.proc
  in
  Printer.prt `Warning
    "Type-checked process:@;@;  @[%a@]@]@;"
    Process.pp p ;

  (* FIXME: do not use hard coded projections *)
  let projections = [Projection.left; Projection.right] in
  let system_name = match system_name with
    | Some lsymb -> lsymb
    | None -> L.mk_loc Location._dummy "default"
  in
  let table,system_name = System.declare_empty table system_name projections in

  (* we register the init action before parsing the system *)
  let init_descr = Action.{
      exec_model;
      name      = Symbols.init_action;
      action    = [];
      input     = Symbols.dummy_channel;
      indices   = [];
      condition = ([], Term.mk_true);
      updates   = Macros.get_init_states table;
      output    = (Symbols.dummy_channel, Term.empty);
      globals   = []; }
  in
  let table, _, _ =
    System.register_action table system_name init_descr
  in

  (* Translate the process. *)
  let tproc, table = preprocess p projs time table in
  let () =
    Printer.prt `Warning "Pre-processed system:@;@;%a" pp_tproc tproc
  in
  let bound_variables = bound_variables tproc in
  let locks = locks projs tproc in
  let conflicts = conflicts table projs bound_variables locks tproc in
  let () =
    if Hashtbl.length conflicts = 0 then
      Printer.prt `Warning "No conflict found."
    else
      Printer.prt `Warning
        "@[<2>Found %d conflicts :@ %a+ symmetries.@]@."
        (Hashtbl.length conflicts)
        (Utils.pp_hashtbl
           (fun fmt i j -> if i <= j then Format.fprintf fmt "%d/%d@ " i j))
        conflicts
  in
  let labels = make_labels (fun id -> Hashtbl.mem conflicts id) tproc in
  let cuts = find_cuts tproc labels in
  let action_names = name_cuts tproc cuts in
  let future_actions = make_future_actions tproc action_names in
  let () =
    Printer.prt `Warning
      "Pre-processed system with end of blocks marked:@;@;%a"
      (pp_tproc_with_cuts cuts) tproc
  in

  (* Translate to a system of actions. *)
  let penv = init_penv system_name projs time exec_model table in
  let table =
    process_system_decl (L.loc proc) tproc penv action_names future_actions
  in

  check_actions_all_def table tproc;

  let table = Lemma.add_depends_mutex_lemmas table system_name in

  Printer.pr "%a" (System.pp_system table) system_name;
  table
