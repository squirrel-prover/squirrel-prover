
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
  id_left = Term.Left ; id_right = Term.Right
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

let id_left j = j.id_left
let id_right j = j.id_right

let get_env j = j.env

let get_systems j = j.id_left, j.id_right

let get_biframe j = j.frame

let set_biframe j f = { j with frame = f }

let get_frame proj j =
  (* TODO the current pi_elem won't be enough when we want full
   * support of macros and left(_) and right(_) operators.
   *
   * For example, with the bi-term diff(right(output@A),left(output@A))
   * the left projection should be right(output@A) which should be
   * interpreted (e.g. during macro expansion) as the output of action
   * A in the right system. *)
  List.map (pi_elem proj) j.frame

let get_right_frame j = List.map (pi_elem j.id_right) j.frame
