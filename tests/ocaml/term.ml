(** Unit tests for the {!Term} module. *)

open Squirrelcore

let tests = [
  "fresh_forall", `Quick, begin fun () ->
    let x = Vars.make_fresh Type.tindex "i" in
    let y = Vars.make_fresh Type.tindex "i" in
    let t1 =
      Term.mk_forall ~simpl:false [x;y]
        (Term.mk_eq ~simpl:false (Term.mk_var x) (Term.mk_var y))
    in
    let t2 =
      Term.mk_forall ~simpl:false [x;y]
        (Term.mk_eq ~simpl:false (Term.mk_var x) (Term.mk_var x))
    in
    Format.printf "t1 = %a@." Term.pp t1 ;
    Format.printf "t2 = %a@." Term.pp t2 ;
    assert (t1 <> t2)
  end
]
