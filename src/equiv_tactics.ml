open Term

type tac = EquivSequent.t Tactics.tac

module T = Prover.EquivTactics

(** Wrap a tactic expecting an equivalence goal (and returning arbitrary
  * goals) into a tactic expecting a general prover goal (which fails
  * when that goal is not an equivalence). *)
let only_equiv t (s : Prover.Goal.t) sk fk =
  match s with
  | Prover.Goal.Equiv s -> t s sk fk
  | _ -> fk (Tactics.Failure "Equivalence goal expected")

(** Tactic that succeeds (with no new subgoal) on equivalences
  * where the two frames are identical. *)
let refl (s : EquivSequent.t) sk fk =
  if EquivSequent.get_left_frame s = EquivSequent.get_right_frame s then
    sk [] fk
  else
    fk (Tactics.Failure "Frames not identical")

let () =
  T.register "refl"
    ~help:"Closes a reflexive goal."
    (only_equiv refl)
