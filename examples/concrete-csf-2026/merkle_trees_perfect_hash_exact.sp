include Logic.
include Int.
include Real.
open Int.

op max (i : int) (j : int) = if i > j then i else j.

op pfst ['a 'b] ( (x,y) : 'a * 'b ) = x.
op psnd ['a 'b] ( (x,y) : 'a * 'b ) = y.

(* ------------------------------------------------------------------- *)
system null.

(* ------------------------------------------------------------------- *)
(* a finite type indexing leaves of the Merkle tree *)
type lval[serializable,finite].

(* ------------------------------------------------------------------- *)
(* Abstract formatters, composed of a serializer and a corresponding
   parser. *)
op serialize ['a] : 'a -> message.
op parse     ['a] : message -> 'a.

op valid_formater ['a] = forall x : 'a, parse (serialize x) = x.

(* ------------------------------------------------------------------- *)
(* We assume that we have sound formatters for some useful types. *)

(* tagging function *)
exact axiom format_tag  : valid_formater[string * message].

(* serialize a leaf value of type `lval` *)
exact axiom format_lval  : valid_formater[lval].

(* serialize a pair of bitstrings as a bitstring *)
exact axiom format_pair : valid_formater[message * message].

(* ------------------------------------------------------------------- *)
(* Encoding functions and related lemmas *)

(* encoding to hash a leaf *)
op encode_leaf (x : lval) = serialize ("leaf", serialize x).

(* encoding to hash a node *)
op encode_node (x : message * message) = serialize ("node", serialize x).

exact lemma encode_leaf_node x y : encode_leaf x = encode_node y => false.
Proof. 
  intro H. 
  apply (f_apply parse[string*message]) in H.
  rewrite !format_tag in H.
  discriminate H.
Qed.

exact lemma encode_node_leaf x y : encode_node y = encode_leaf x => false.
Proof. 
  rewrite eq_sym.
  apply encode_leaf_node.
Qed.

exact lemma encode_leaf_injective : forall x y, encode_leaf x = encode_leaf y => x = y.
Proof. 
  intro x y H. 
  apply (f_apply parse[string*message]) in H.
  rewrite !format_tag in H.
  destruct H as [_ H].
  apply (f_apply parse[lval]) in H.
  rewrite !format_lval in H.
  auto.
Qed.

exact lemma encode_node_injective : forall x y, encode_node x = encode_node y => x = y.
Proof. 
  intro x y H. rewrite /encode_node in H => /=.
  apply (f_apply parse[string*message]) in H.
  rewrite !format_tag in H.
  apply f_apply psnd in H.
  rewrite /psnd /= in H.
  apply (f_apply parse[message*message]) in H.
  rewrite !format_pair in H.
  auto.
Qed.

(* ------------------------------------------------------------------- *)
(* Hash functions *)

(* a hash function, supposed perfect (which is of course unrealistic) *)
op fhash : message -> message.

exact axiom fhash_injective : forall x y, fhash x = fhash y => x = y.

(* ------------------------------------------------------------------- *)
(* Trees *)

inductive tree =
| Leaf : lval -> tree
| Node : tree -> tree -> tree.

(* ------------------------------------------------------------------- *)
let rec depth (t : tree) with
| Leaf m -> 0
| Node l r -> max (depth l) (depth r) + 1.
Proof. split; intro > <-; discriminate. Qed.

(* Count the number of node in `t` (leaves do not count). *)
let rec size (t : tree) with
| Leaf m -> 1
| Node l r -> 1 + size l + size r.
Proof. split; intro > <-; discriminate. Qed.

(* ------------------------------------------------------------------- *)
(* Hash of a tree:
   - uses `encode_leaf` to encode a leaf before hashing it
   - uses `encode_node` to combine the hashes of the left and right
     sub-trees before hashing them. *)
let rec hash_tree (t : tree) = fhash (hash_tree0 t)
termination_by (t,1)

and hash_tree0 t with
| Leaf m -> encode_leaf m
| Node l r -> encode_node (hash_tree l, hash_tree r)
termination_by (t,0).
Proof.
  (split; 2:split);
  [1,2: intro > <-; discriminate | 3: intro >; discriminate].
Qed.

(* ------------------------------------------------------------------- *)
inductive side = Left : side | Right : side.

exact lemma right_left : (Right = Left) = false.
Proof. 
  rewrite eq_iff.
  split;2:auto.
  intro H; discriminate H.
Qed.

op select ['a] (l,r:'a) (side : side) = if side = Left then l else r.

inductive nat = Z : nat | S : nat -> nat.

(* A membership proof *)
inductive proof =
| Emp : proof
| Cons : side -> message -> proof -> proof.
(* `Cons s h p`: `s` is the side we go down
    in the tree, and `h` is the hash of the other side. *)

let rec length (p : proof) with
| Emp -> Z
| Cons _ _ p' -> S (length p').
Proof. intro > <-; discriminate. Qed.

(* Descend in `t` following the proof `p`, and retrieve the
   corresponding sub-tree. *)
let rec lookup ( (p,t) : proof * tree) : tree with
| (Emp, _) -> t
| (Cons side _ psub, Node l r) -> lookup (psub, select l r side)
| (Cons _ _ _, Leaf _) -> witness.
Proof. intro > <-; discriminate. Qed.

(* If `p` proves that a tree `tsub` with hash `hsub` is a
   sub-tree of `t`, computes `hash_tree t`. *)
let rec hash_path (hsub : message) (p : proof) : message  with
| Emp -> hsub
| Cons side ha psub -> 
  let hb = hash_path hsub psub in
  let h0 = select hb ha side in
  let h1 = select ha hb side in
  fhash (encode_node (h0, h1)).
Proof. intro > <-; discriminate. Qed.

(* ------------------------------------------------------------------- *)
(* Checks that `p` proves that `tsub` (with hash `hsub`) is a sub-tree
   of a tree `t` (with hash `h`).
   Crucially, this check does not have access to `tsub` nor `t`, and
   only uses their hashes `hsub`, `hroot`, and a path of length at-most
   `depth t`. *)
let verify (hsub : message) (p : proof) (h : message) : bool = 
  h = hash_path hsub p.

(* ------------------------------------------------------------------- *)

exact lemma hash_tree_injective (t,t' : tree) :
  hash_tree t = hash_tree t' => t = t'.
Proof.
  generalize t; induction t'.
  + intro x t H.
    rewrite /hash_tree /hash_tree0 in H.
    apply fhash_injective in H.
    revert H; case t; 3 : auto.
    - intro a H.
      apply encode_leaf_injective in H.
      auto.

    - intro tl tr H.
      by apply encode_node_leaf in H.

  + intro tl' tr' IHl IHr t H.
    rewrite /hash_tree in H.
    apply fhash_injective in H.
    revert H; case t; 3 : auto.
    - intro x H.
      by apply encode_leaf_node in H.

    - intro tl tr H.
      apply encode_node_injective in H.
      destruct H as [Hr Hl].
      apply IHl in Hl.
      apply IHr in Hr.
      auto.
Qed.

(* If we accept `p` of length `n` as a proof that `tsub` is a sub-tree
   of `t` then `tsub` is a sub-tree of `t` following the path `p`. *)
exact lemma verify_correct (n : nat) (p : proof) (t : tree) (tsub : tree) :
  length p = n =>
  verify (hash_tree tsub) p (hash_tree t) =>
  lookup (p,t) = tsub.
Proof.
  generalize p t; induction n.

  (* `n = Z` *)
  + intro p t.
    (* since `n = Z`, we have `p = Emp` *)
    case p; 3 : auto;  id=> @/length //=; 2: intro > H; discriminate H.

    (* evaluates `verify ...` into `hash_tree tsub = hash_tree t` *)
    rewrite /verify /hash_path /lookup /= => H.

    (* apply auxiliary lemma proving that
      `hash_tree t = hash_tree tsub => t = tsub` *)
    by apply hash_tree_injective.

  (* `n = S n0` *)
  + intro n0 IH p t.
    (* since `n = S n0`, we have `p = Cons i hj pi` (intuitively, `j = 1 - i`) *)
    case p; 3 :auto;  id=> @/length //=; 1: intro > H; discriminate H.
    intro i hj pi [L] H.

    (* `verify` checks that the hash of `t` equals to hash
        reconstructed from the proof `p` *)
    rewrite /verify /= in H. rewrite /hash_path in H.

    (* apply injectivity of the hash function *)
    apply fhash_injective in H.

    (* case analysis over `t` *)
    revert H; case t; 3 : auto.
      (* case `t = Leaf _` *)
    - intro l H /=.
      (* impossible since our encoding is non-ambiguous *)
      by apply encode_leaf_node in H.

     (* `t = Node(t0,t1)` *)
    - intro t0 t1 H.

      (* `lookup` descends in the branch `ti` of `t`, and we must
          prove that `lookup (pi, ti) = tsub` *)
      rewrite /lookup.

      apply encode_node_injective in H.
     (* after some basic reasoning on the encoding, we know that:
        `hash_tree ti = hash_path (hash_tree tsub) pi`
        `hash_tree tj = hj` *)

      (* by induction hypothesis, it is sufficient to prove that `pi`
         proves that `tsub` is a sub-tree of `ti` *)
      apply IH; 1:auto.
      rewrite /verify.

      (* which we know thanks to `H` *)
      revert H; case i; [1,3:auto | 2: by rewrite /select right_left /=].
Qed.
