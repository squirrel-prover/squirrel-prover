include Real. open Real.
include Int. open Int.

op phi : bool.
op psi : bool.

op phi_bnd : Real.t.
op psi_bnd : Real.t.

axiom phi_ax @system:any : phi <: phi_bnd.
axiom psi_ax @system:any : psi <: psi_bnd.

lemma _ @system:any : phi && psi <: phi_bnd + psi_bnd.
Proof. 
  (* we can give the mass to be used on the left *)
  split phi_bnd. 
  + by apply phi_ax.
  + weak psi_bnd. 
    by rewrite Real.add_assoc Real.add_comm Real.add_assoc. 
    by apply psi_ax.
Qed.

lemma _ @system:any : phi && psi <: phi_bnd + psi_bnd.
Proof. 
  (* Otherwise, `split` exploits the shape of the bound for
     case-splitting. *)
  split. 
  + by apply phi_ax.
  + by apply psi_ax.
Qed.
