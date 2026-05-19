include Logic.
include Int. 
include Real. 

open Int.
open Real.

op max (i : int) (j : int) = if i > j then i else j.

op pfst ['a 'b] ( (x,y) : 'a * 'b ) = x.
op psnd ['a 'b] ( (x,y) : 'a * 'b ) = y.

(* ------------------------------------------------------------------- *)
system null.

(* ------------------------------------------------------------------- *)
(* a finite type indexing leaves of the Merkle tree *)
type lval[serializable, finite].

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

exact lemma encode_leaf_injective : 
  forall x y, encode_leaf x = encode_leaf y => x = y.
Proof. 
  intro x y H. 
  apply (f_apply parse[string*message]) in H.
  rewrite !format_tag in H.
  destruct H as [_ H].
  apply (f_apply parse[lval]) in H.
  rewrite !format_lval in H.
  auto.
Qed.

exact lemma encode_node_injective : 
  forall x y, encode_node x = encode_node y => x = y.
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

(* Type of the keys used to indexed our hash function. *)
type hkey[serializable].

(* We consider a fixed key of type `hhey` *)
name k : hkey.

(* a keyed hash function *)
op fhash : message -> hkey -> message.

op e_col : Real.t.

exact axiom e_col_pos : e_col >= of_int 0.

(* We assume that for any polynomial-time computable messages `x` and
   `y`, the probability that `x` and `y` form a collision for `fhash` on
   key `k` is bound by `e_col`. *)
axiom fhash_cr (x, y : hkey -> message[adv]) : fhash (x k) k = fhash (y k) k => x k = y k <: e_col.

(* Allow general higher-order unification, to allow the unifier to
   infer `x` without manually η-expanding `k` *)
set higherOrderUnification="All".

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
     sub-trees before hashing them. 

   We admit that `hash_tree` and `hash_tree0` can be computed in
   polynomial-time. *)
let rec hash_tree ~admit_ptime k (t : tree) = fhash (hash_tree0 k t) k
termination_by (t,1)

and hash_tree0 ~admit_ptime k (t : tree) with
| Leaf m -> encode_leaf m
| Node l r -> encode_node (hash_tree k l, hash_tree k r)
termination_by (t,0).
Proof. 
  (split; 2:split); 
  [1,2: intro > <-; discriminate | 3: intro >; discriminate].
Qed.

(* ------------------------------------------------------------------- *)
inductive side = Left : side | Right : side.

let side_match (f_Left,f_Right : Real.t) (x : side) : Real.t with
  | Left -> f_Left
  | Right -> f_Right.


exact lemma right_left : (Right = Left) = false.
Proof. 
  rewrite eq_iff.
  split;2:auto.
  intro H; discriminate H.
Qed.

op select ['a] (l,r:'a) (side : side) = if side = Left then l else r.

inductive nat = Z : nat | S : nat -> nat.

namespace Real.
  let rec of_nat (n : nat) with
  | Z   -> Real.z
  | S n -> of_int 1 + of_nat n.
  Proof. intro > <-. discriminate. Qed.

  exact lemma [any] eq_leq (x,y:Real.t): x = y => x <= y. 
  Proof. smt ~no_macros. Qed.
end Real.
open Real.                      (* export of_nat in the root namespace *)

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
   sub-tree of `t`, computes `hash_tree t`. 
   We admit that `hash_path` can be computed in polynomial-time. *)
let rec hash_path ~admit_ptime (hsub : message) (p : proof) : message  with
| Emp -> hsub
| Cons side ha psub -> 
  let hb = hash_path hsub psub in
  let h0 = select hb ha side in
  let h1 = select ha hb side in
  fhash (encode_node (h0, h1)) k.
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
global lemma case_const_tree @set:'P (t : tree[const,adv]) :
  (Exists (l:_[const,adv]), [t = Leaf l <: z]) \/ (Exists (t1, t2:_[const,adv]), [t = Node t1 t2 <: z]).
Proof.
   case t => >;[ 1: by left; exists x | 2 : by right; exists x; exists x0].
Qed.

(* ------------------------------------------------------------------- *)
let tree_error t = of_int (size t) * e_col.
let path_error n = of_nat n * e_col.

(* ------------------------------------------------------------------- *)
global lemma hash_tree_injective
  @system:default
  (t : tree[adv], t':tree[adv,const])
:
  [hash_tree k t = hash_tree k t' => t = t' <: tree_error t'].
Proof.
  generalize t' t; induction ~concrete ~general.
  intro t' IH t.
  have [[l C]| [t1' t2' C]] := case_const_tree t'; rewrite C in *.
  + intro H => {IH}.
    rewrite /hash_tree /hash_tree0 in H.
    apply localize(fhash_cr _ _) in H=> //=.
    revert H; case t=> //=; 3 : by rewrite /tree_error /size.
    - intro a H. 
      apply encode_leaf_injective in H.
      auto.

    - intro x x0 H.
      by apply encode_node_leaf in H.

  + intro H.                    (* Note: case introduces more *)
    rewrite /hash_tree in H.
    apply localize(fhash_cr _ _) in H=> //=.
    revert H.
    case ~tags t <: z, ((of_int (size t') * e_col) - e_col); 3: by rewrite C.
    - intro H /=.
      by apply encode_leaf_node in H.

    - intro H /=.
      apply encode_node_injective in H.
      destruct H as [Hl Hr].

      apply localize(IH t1' x) in Hl; 1:discriminate.
      apply localize(IH t2' x0) in Hr; 1:discriminate.
      rewrite Hl Hr //=; true.
      rewrite C /tree_error /size; smt ~no_macros.
Qed.
    (* Remark on the ~tags of the case tactic:
       The `tags` exploits the computational information of `t`
       (e.g., when `t = Node x x0`, we obtain that `x` and `x0` are
       `adv` since `t` is `adv`). This has the effect that `x,x0` are
       automatically introduced, because `adv` cannot be attached to a
       local quantification. *)

global lemma case_const_nat @set:'P (n : nat[const]) :
  ([n = Z <: z]) \/ 
  (Exists (n0:_[const]), [n = S n0 <: z]).
Proof.
   case n => >. 
   + by left. 
   + by right; exists x.
Qed.


(* If we accept `p` of length `n` as a proof that `tsub` is a sub-tree 
   of `t` then `tsub` is a sub-tree of `t` following the path `p`. *)
global lemma verify_correct
  @system:default
  (n : nat[const]) (p : proof[adv]) (t : tree[adv]) (tsub : tree[const,adv])
:
  [length p = n =>
   verify (hash_tree k tsub) p (hash_tree k t) => 
   lookup (p,t) = tsub 
   <: tree_error tsub + path_error n].
Proof. 
  generalize p t; induction ~concrete ~general n.
  intro n IH p t.
  have [C | [n0 C]] := case_const_nat n; rewrite C in *.

  (* `n = Z` *)
  + (* since `n = Z`, we have `p = Emp` *)
    (case p <: tree_error tsub, z; 3:auto) => @/length //=; 2: intro > H; discriminate H.

    (* evaluates `verify ...` into `hash_tree tsub = hash_tree t` *)
    rewrite /verify /hash_path /lookup /= => H.

    (* apply auxiliary lemma proving that 
      `hash_tree t = hash_tree tsub => t = tsub` Cost: `|tsub| * e_col` *)
    by apply hash_tree_injective.

  (* `n = S _` *)
  + (case ~tags p <: z, tree_error tsub + path_error n; 3 : by rewrite C) => @/length //=; 1: intro > H; discriminate H.
    intro (* i jh pi *) [L] H.

    (* `verify` checks that the hash of `t` equals to hash
        reconstructed from the proof `p` *)
    rewrite /verify /= in H.
    
    (* apply injectivity of the hash function Cost: `e_col` *)
    apply localize(fhash_cr _ _) in H=> //=.

    (* case analysis over `t` Cost: all error mass is sent to case `t = Node(_,_)` *)
    revert H; case ~tags t <: z, (tree_error tsub  + path_error n) - e_col; 3:auto.
      (* case `t = Leaf _` *)
    - intro H /=.
      (* impossible since our encoding is non-ambiguous Cost: `0` *)
      by apply encode_leaf_node in H.
    
     (* `t = Node(t0,t1)` 
        Because `case ~tags` must automatically names variables, we 
        have less agreable names for the sub-trees of `t`: 
        `x2` should be replaced by `t0`, and `x3` by `t1` *)
    - intro H. 

      (* `lookup` descends in the branch `ti` of `t`, and we must
           prove that `lookup (pi, ti) = tsub` *)
      rewrite /lookup.

      apply encode_node_injective in H.
     (* after some basic reasoning on the encoding, we know that:
        `hash_tree ti = hash_path (hash_tree tsub) pi`
        `hash_tree tj = hj` *)

      (* by induction hypothesis, it is sufficient to prove that `pi`
         proves that `tsub` is a sub-tree of `ti` Cost: `|ti| * e_col` *)
      apply IH n0; 1:discriminate.
      rewrite /verify.

      (* which we know thanks to `H` *)
      revert H; case x; [1:auto | 2: by rewrite /select right_left /=].
      
      (* Cost: basic bound reasoning *)
      rewrite C /path_error /of_nat /tree_error /=; smt ~no_macros.
Qed.
