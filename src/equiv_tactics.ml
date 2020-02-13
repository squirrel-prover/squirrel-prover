open Term

type tac = EquivSequent.t Tactics.tac

module T = Prover.EquivTactics

(** {2 Utilities} *)

exception Out_of_range

(** When [0 <= i < List.length l], [nth i l] returns [before,e,after]
  * such that [List.rev_append before (e::after) = l] and
  * [List.length before = i].
  * @raise Out_of_range when [i] is out of range. *)
let nth i l =
  let rec aux i acc = function
    | [] -> raise Out_of_range
    | e::tl -> if i=0 then acc,e,tl else aux (i-1) (e::acc) tl
  in aux i [] l

(** {2 Tactics} *)

(** Wrap a tactic expecting an equivalence goal (and returning arbitrary
  * goals) into a tactic expecting a general prover goal (which fails
  * when that goal is not an equivalence). *)
let only_equiv t (s : Prover.Goal.t) sk fk =
  match s with
  | Prover.Goal.Equiv s -> t s sk fk
  | _ -> fk (Tactics.Failure "Equivalence goal expected")

(** Wrap a tactic expecting and returning equivalence goals
  * into a general prover tactic. *)
let pure_equiv t s sk fk =
  let t' s sk fk =
    t s (fun l fk -> sk (List.map (fun s -> Prover.Goal.Equiv s) l) fk) fk
  in
  only_equiv t' s sk fk

(** Tactic that succeeds (with no new subgoal) on equivalences
  * where the two frames are identical. *)
let refl (s : EquivSequent.t) sk fk =
  if EquivSequent.get_frame Term.Left s = EquivSequent.get_frame Term.Right s
  then
    sk [] fk
  else
    fk (Tactics.Failure "Frames not identical")

let () =
  T.register "refl"
    ~help:"Closes a reflexive goal."
    (only_equiv refl)

(** Function application *)
let fa i s sk fk =
  let expand : type a. a Term.term -> EquivSequent.elem list = function
    | Fun (f,l) ->
        List.map (fun m -> EquivSequent.Message m) l
    | Diff _ ->
        Tactics.soft_failure
          (Tactics.Failure "No common construct")
    | _ ->
        Tactics.soft_failure
          (Tactics.Failure "Unsupported: TODO")
  in
  let expand = function
    | EquivSequent.Message e -> expand (Term.head_normal_biterm e)
    | EquivSequent.Formula e -> expand (Term.head_normal_biterm e)
  in
  match nth i (EquivSequent.get_biframe s) with
    | before, e, after ->
        begin try
          let biframe = List.rev_append before (expand e @ after) in
          sk [EquivSequent.set_biframe s biframe] fk
        with
          | Tactics.Tactic_Soft_Failure err -> fk err
        end
    | exception Out_of_range ->
        fk (Tactics.Failure "Out of range position")

let () =
  T.register_general "fa"
    ~help:"Break function applications."
    (function
       | [Prover.Int i] -> pure_equiv (fa i)
       | _ -> Tactics.hard_failure (Tactics.Failure "Integer expected"))
