include Logic.

(* ------------------------------------------------------------------- *)
op serialize ['a] : 'a -> message.
op parse     ['a] : message -> 'a.

op valid_formater ['a] = forall x : 'a, parse (serialize x) = x.

(* ------------------------------------------------------------------- *)
axiom format_tag @system:any : valid_formater[string * message].

(* ------------------------------------------------------------------- *)
op encode (x : message) = serialize ("1", x).

lemma _ @system:any x y : encode x = encode y => x = y.
Proof. 
  intro H. 
  apply (f_apply parse[string*message]) in H.
  rewrite !format_tag in H.
  auto.
Qed.
