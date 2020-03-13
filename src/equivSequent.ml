
type elem =
  | Formula of Term.formula
  | Message of Term.message

let pp_elem ppf = function
  | Formula t -> Term.pp ppf t
  | Message t -> Term.pp ppf t

let pi_term projection tm = Term.pi_term ~bimacros:true ~projection tm

let pi_elem s = function
  | Formula t -> Formula (pi_term s t)
  | Message t -> Message (pi_term s t)

let pp_frame ppf (l:elem list) =
  Fmt.pf ppf "%a"
    (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@ ") pp_elem)
    l

let pp_frame_numbered ppf (l:elem list) =
  let max_i = List.length l - 1 in
  List.iteri (fun i elem ->
      if i < max_i then
        Fmt.pf ppf "%i: %a,@ " i pp_elem elem
      else
        Fmt.pf ppf "%i: %a" i pp_elem elem
    )
    l


let apply_subst_frame subst f =
List.map (function Formula f -> Formula (Term.subst subst f)
                 | Message t ->Message (Term.subst subst t)) f


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
  hypothesis_frame : elem list;
  frame : elem list;
  system : Action.system;
}

let init system env l = {
  env = env ; frame = l ; hypothesis_frame = [];
  system = system;
}

type sequent = t

let pp ppf j =
  if j.env <> Vars.empty_env then
    Fmt.pf ppf "@[Variables: %a@]@;" Vars.pp_env j.env ;
  if j.hypothesis_frame <> [] then
    Fmt.pf ppf "@[Hypothesis: %a@]@;" pp_frame j.hypothesis_frame ;
  Fmt.pf ppf "%a" pp_frame_numbered j.frame

let pp_init ppf j =
  if j.env <> Vars.empty_env then
    Fmt.pf ppf "forall %a,@ " Vars.pp_env j.env ;
  Fmt.pf ppf "%a"
    (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@ ") pp_elem)
    j.frame

let id_left j = let open Action in j.system.left.id
let id_right j = let open Action in j.system.right.id

let get_env j = j.env

let set_env e j = {j with env = e}

let get_system j = j.system

let get_biframe j = j.frame

let get_hypothesis_biframe j = j.hypothesis_frame

let set_hypothesis_biframe j f = { j with hypothesis_frame = f}

let set_biframe j f = { j with frame = f }

let get_frame proj j = List.map (pi_elem proj) j.frame

let apply_subst subst s =
  { s with frame = apply_subst_frame subst s.frame;
           hypothesis_frame = apply_subst_frame subst s.hypothesis_frame }
