(** Goal mode input types:
    - [Gm_goal f] : declare a new goal f.
    - [Gm_proof] : start a proof. *)

type gm_input = Gm_goal of string * Term.formula | Gm_proof
