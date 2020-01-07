(** Indices are used to generate arbitrary families of terms, and thus duplicate
  * of actions. Indices are never instantiated and have no specific structure,
  * they are simply variables. *)

type t = Vars.var

let pp = Vars.pp

(** Index substitutions. *)
type subst = (t*t) list

let pp_subst ppf subst =
  Fmt.list
    ~sep:(fun ppf () -> Fmt.pf ppf "@,")
    (fun ppf (i,j) ->
       Fmt.pf ppf "%a->%a" pp i pp j)
    ppf
    subst

