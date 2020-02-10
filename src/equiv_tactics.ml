open Term

type tac = EquivSequent.t Tactics.tac

module T = Prover.EquivTactics

let only_equiv t (s : Prover.Goal.t) sk fk =
  match s with
  | Prover.Goal.Equiv s -> t s sk fk
  | _ -> fk (Tactics.Failure "Equivalence goal expected")

let refl (s : EquivSequent.t) sk fk =
    if EquivSequent.get_left_frame s = EquivSequent.get_right_frame s then
      sk [] fk
    else
      fk (Tactics.Failure "Frame not reflexive")

let () =
    T.register "refl"
    ~help:"Closes a reflexive goal."
    (only_equiv refl)
