(** Support for bullets and braces in proof scripts. *)

(** A proof is a tree of goals, each goal node having subgoals as children.

    We view a proof with bullets as one such tree where some edges are
    decorated:
     - for some nodes, all edges from the node to its children are decorated
       by the same bullet symbol;
     - if two nodes of the previous case are decorated with the same
       bullet symbol, they must be disjoint (one is not the ancestor of
       the other);
     - additionnally, some edges may be decorated by the brace symbol.

    When interactively constructing the proof tree, bullet symbols must
    be used to mark the beginning of subproofs corresponding to the
    children of the first case above. Opening and closing braces are used
    to delimit the proof script corresponding to a node of the third
    case above. Bullets and braces can be combined for some subgoals;
    in that case, the bullet symbol must precede the opening brace.

    This is realized by maintaining a path indicating a position in the
    decorated proof tree, where we consider edge decorations as virtual
    nodes, to distinguish the position before or after the decoration
    along some edge. We also introduce special paths which indicate
    that closing braces are expected before moving on to a next path. *)

type bullet = string

type path =
  | Empty
      (** Path corresponding to finished proof, with no remaining goal. *)
  | Step of
      { path     : path ;
        position : int ;
        width    : int ;
        bullet   : [ `None | `Before of bullet | `After of bullet ] ;
        (** The bullet status can indicate that no bullet is being
            used, that the path progresses after a bullet, or is before
            an expected bullet. As a special case,
            [`None] indicates an unknown status for the first step
            of a path pointing to a first sibling. *)
        brace    : bool
        (** The brace status indicates whether a brace decoration is
            present: [true] means that a brace symbol has been encountered
            and will have to be closed, [false] means that no brace symbol
            has been encountered. *) }
      (** Paths are represented in reverse order:
          [Step s] denotes the path [s.path] going from the root to some
          node followed by some edge going to child number [s.position]
          among [s.width] siblings. *)
  | Brace_needed of path
      (** Indicates that a closing brace is needed before going
          to a new path. Can only occur at toplevel. *)

(** [unused_bullet b p = true] iff bullet [b] is unused in [p]. *)
let rec unused_bullet b = function
  | Empty -> true
  | Brace_needed path -> unused_bullet b path
  | Step {path;bullet} ->
      unused_bullet b path &&
      match bullet with
        | `None -> true
        | `Before b' | `After b' -> b <> b'

(** Well-formedness of inner paths. *)
let rec inner_well_formed = function
  | Empty -> true
  | Brace_needed _ -> false
  | Step {path;position;width;bullet} ->
      0 < position  &&
      position <= width &&
      inner_well_formed path &&
      match bullet with
        | `None -> true
        | `Before b | `After b -> unused_bullet b path

(** Well-formedness of toplevel paths. *)
let rec well_formed = function
  | Brace_needed p -> well_formed p
  | p -> inner_well_formed p

(** Initial path, pointing to a single initial goal with no decoration. *)
let initial_path =
  Step { path = Empty ; position = 1 ; width = 1 ;
         bullet = `None ; brace = false }

(** Final path, corresponding to no remaining goals. *)
let empty_path = Empty

(** Indicates that there is no remaining subgoal. *)
let is_empty p = p = Empty

(*------------------------------------------------------------------*)
type bullet_error =
  | Decoration_not_allowed
  (** Multiple bullets or braces, bullet after brace,
      closing brace on unclosed goal or on goal without an open brace,
      or attempt to decorate empty path. *)

  | Closing_brace_needed
  (** Raised if some operation is attempted when a closing brace is needed. *)

  | Bullet_expected
  (** Raised if some operation is attempted when a bullet is expected. *)
  
exception Error of bullet_error

let error e = raise (Error e)

(*------------------------------------------------------------------*)
(** Update path by opening a brace. *)
let open_brace = function
  | Empty -> error Decoration_not_allowed
  | Brace_needed _ -> error Closing_brace_needed
  | Step s ->
      if s.brace then error Decoration_not_allowed ;
      Step { s with brace = true }

(** Update path by opening a bullet. *)
let open_bullet b = function
  | Empty -> error Decoration_not_allowed
  | Brace_needed _ -> error Closing_brace_needed
  | Step s ->
      if s.brace = true then error Decoration_not_allowed ;
      match s.bullet with
        | `None when s.position = 1 && unused_bullet b s.path ->
            Step { s with bullet = `After b }
        | `Before b' when b = b' -> Step { s with bullet = `After b }
        | _ -> error Decoration_not_allowed

(** Indicates whether [close_goal] and [expand_goal] are allowed,
    i.e. if a tactic can be evaluated on the current goal. *)
let tactic_allowed = function
  | Brace_needed _ | Step { bullet = `Before _ } -> false
  | _ -> true

(** Close brace. This is only valid just after that a goal with an open
    brace has been closed. *)
let close_brace = function
  | Brace_needed p -> p
  | _ -> error Decoration_not_allowed

(** Return path to next goal after closing current goal.
    This involves going up the tree for an arbitrary number
    of steps (possibly zero) then down to a next sibling,
    but this traversal will be interrupted by braces that need
    to be closed. *)
let rec close_goal = function
  | Empty -> Empty
  | Brace_needed _ -> error Closing_brace_needed
  | Step {path;position;width;bullet;brace} ->
      if position = width then
        match bullet with
          | `Before _ -> error Bullet_expected
          | _ ->
            let newpath = close_goal path in
              if brace then Brace_needed newpath else newpath
      else
        let newpath =
          Step { path ; width ; position = position+1 ; brace = false ;
                 bullet = match bullet with
                   | `Before _ -> error Bullet_expected
                   | `After b -> `Before b
                   | `None -> `None }
        in
          if brace then Brace_needed newpath else newpath

let expand_goal width = function
  | path when width = 0 -> close_goal path
  | Step { bullet = `Before _ } -> error Bullet_expected
  | path ->
      Step { path ; position = 1 ; width ; bullet = `None ; brace = false }

(** Pretty-printing for debugging. *)
let rec pp fmt = function
  | Empty -> Format.pp_print_string fmt "@"
  | Brace_needed p -> Format.fprintf fmt "%a.}" pp p
  | Step s ->
      Format.fprintf fmt "%a[%d/%d]%s%s"
        pp s.path s.position s.width
        (match s.bullet with `None -> "" | `Before s -> "."^s | `After s -> s)
        (if s.brace then "{" else "")

(* --------- TESTS ---------  *)

let verbose = false

let (|>) x f =
  if verbose then Format.printf "%a@." pp x ;
  assert (well_formed x) ;
  f x

let pass _ =
  if verbose then Format.printf "OK@.@."

let check_fail exn f p =
  try ignore (f p) ; assert false with e when e = exn -> pass ()

let check_empty p =
  assert (p = Empty) ;
  pass ()

let%test_unit _ =
  (* One goal expansion is possible. *)
  initial_path |> expand_goal 3 |> pass

let%test_unit _ =
  (* A subgoal can be closed. *)
  initial_path |>
  expand_goal 3 |>
  close_goal |>
  pass

let%test_unit _ =
  (* A non-trivial proof can be completed. *)
  initial_path
    |> expand_goal 3
    |> close_goal
    |> expand_goal 1
    |> close_goal
    |> close_goal
    |> check_empty

let%test_unit _ =
  (* A bullet can be used. *)
  initial_path
    |> open_bullet "*"
    |> close_goal
    |> pass

let%test_unit _ =
  (* Bullets can be used to decorate two siblings. *)
  initial_path |> expand_goal 2
    |> open_bullet "*"
    |> expand_goal 1 |> expand_goal 1 |> close_goal
    |> open_bullet "*"
    |> close_goal
    |> pass

let%test_unit _ =
  (* If used, bullets must be used for previous sibling. *)
  initial_path |> expand_goal 2
    |> expand_goal 1 |> expand_goal 1 |> close_goal
    |> check_fail (Error Decoration_not_allowed) (open_bullet "*")

let%test_unit _ =
  (* If used, bullets must be used before expanding next sibling. *)
  initial_path |> expand_goal 2
    |> open_bullet "*"
    |> expand_goal 1 |> expand_goal 1 |> close_goal
    |> check_fail (Error Bullet_expected) (expand_goal 1)

let%test_unit _ =
  (* If used, bullets must be used before closing next sibling. *)
  initial_path |> expand_goal 2
    |> open_bullet "*"
    |> expand_goal 1 |> expand_goal 1 |> close_goal
    |> check_fail (Error Bullet_expected) close_goal

let%test_unit _ =
  (* Nested bullets with different symbols are allowed. *)
  initial_path
    |> expand_goal 2
    |> open_bullet "*" |> close_goal
    |> open_bullet "*" |> expand_goal 3
      |> open_bullet "+" |> close_goal
      |> open_bullet "+" |> close_goal
      |> open_bullet "+" |> close_goal
    |> pass

let%test_unit _ =
  (* Nested bullets with same symbol are not allowed. *)
  initial_path
    |> expand_goal 2
    |> open_bullet "*" |> close_goal
    |> open_bullet "*" |> expand_goal 3
      |> check_fail (Error Decoration_not_allowed) (open_bullet "*")

let%test_unit _ =
  (* Disjoint bullets with same symbol are allowed. *)
  initial_path
    |> expand_goal 2
    |> expand_goal 1 |> open_bullet "*" |> close_goal
    |> expand_goal 1 |> open_bullet "*" |> close_goal
    |> check_empty

let%test_unit _ =
  (* Braces can be used. *)
  initial_path |> open_brace |> close_goal |> close_brace
    |> check_empty

let%test_unit _ =
  (* An opened brace must be closed. *)
  initial_path |> expand_goal 2
    |> open_brace |> close_goal
    |> check_fail (Error Closing_brace_needed) close_goal

let%test_unit _ =
  (* Braces can be used directly inside a bullet. *)
  initial_path |> open_bullet "*" |> open_brace
    |> close_goal |> close_brace |> check_empty

let%test_unit _ =
  (* Braces cannot be used directly outside a bullet. *)
  initial_path |> open_brace
    |> check_fail (Error Decoration_not_allowed) (open_bullet "*")

let%test_unit _ =
  (* A brace cannot be opened directly after another. *)
  initial_path |> open_brace |>
    check_fail (Error Decoration_not_allowed) open_brace

let%test_unit _ =
  (* Braces can be nested. *)
  initial_path |> open_brace |> expand_goal 1 |> open_brace
    |> close_goal |> close_brace |> close_brace |> check_empty

let%test_unit _ =
  (* Braces can be nested, again. *)
  initial_path |> expand_goal 2
    |> open_brace |> expand_goal 1 |> open_brace
      |> close_goal |> close_brace |> close_brace
    |> close_goal |> check_empty

let%test_unit _ =
  (* Two nested braces must be separately closed. *)
  initial_path |> expand_goal 2
    |> open_brace |> expand_goal 1 |> open_brace
      |> close_goal |> close_brace
    |> check_fail (Error Closing_brace_needed) close_goal
