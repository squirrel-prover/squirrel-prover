(** Management of bullets and braces in proof scripts. *)

(** Bullet symbols. *)
type bullet = string

(** Path through a proof tree under construction. *)
type path

val pp : Format.formatter -> path -> unit

val initial_path : path

val empty_path : path

val is_empty : path -> bool

val tactic_allowed : path -> bool

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

(*------------------------------------------------------------------*)
(** Close current subgoal. *)
val close_goal : path -> path

(** Expand current subgoal to some number of subgoals.
    Equivalent to [close_goal] when the number of subgoals is zero. *)
val expand_goal : int -> path -> path

val open_bullet : bullet -> path -> path

val open_brace : path -> path

val close_brace : path -> path
