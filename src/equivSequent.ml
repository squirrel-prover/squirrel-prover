
type elem =
  | Formula of Term.formula
  | Message of Term.message

let pp_elem ppf = function
  | Formula t -> Term.pp ppf t
  | Message t -> Term.pp ppf t

let pi_elem = fun s t ->
  match t with
  | Formula t -> Formula (Term.pi_term s t)
  | Message t -> Message (Term.pi_term s t)

(** An equivalence sequent features:
  * - two frames given as a single [frame] containing bi-terms
  *   of sort boolean or message;
  * - an environment [env] listing all free variables with their types;
  * - identifiers for the left and right systems.
  * The corresponding equivalence is obtained by projecting the bi-frame
  * to two frames, interpreting macros wrt the left and right systems
  * respectively. *)
type t = {
  env : Vars.env;
  frame : elem list;
  id_left : Action.system_id;
  id_right : Action.system_id;
}

let init env l = {
  env = env ; frame = l ;
  id_left = Left ; id_right = Right
}

type sequent = t

let pp ppf j =
  if j.env <> Vars.empty_env then
    Fmt.pf ppf "@[Variables: %a@]@;" Vars.pp_env j.env ;
  Fmt.pf ppf "%a"
    (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@ ") pp_elem)
    j.frame

let pp_init ppf j =
  if j.env <> Vars.empty_env then
    Fmt.pf ppf "forall %a,@ " Vars.pp_env j.env ;
  Fmt.pf ppf "%a"
    (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@ ") pp_elem)
    j.frame

let get_env j = j.env

let get_left_frame j = List.map (pi_elem j.id_left) j.frame

let get_right_frame j = List.map (pi_elem j.id_right) j.frame
