
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

type t =
  {
    env : Vars.env;

    frame : elem list;

    id_left : Term.system_id;
    id_right : Term.system_id;
  }

type sequent = t

let pp ppf j =
  let open Fmt in
  if j.env <> Vars.empty_env then
    pf ppf "@[Variables: %a@]@;" Vars.pp_env j.env ;
  pf ppf "@;%a@]"
    (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@ ") pp_elem)
 j.frame

let get_env j = j.env

let get_left_frame j = List.map (pi_elem j.id_left) j.frame

let get_right_frame j = List.map (pi_elem j.id_right) j.frame
