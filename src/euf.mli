open Action
open Process

(* (\** This is [Process.block], but using the types of module [Term] instead of
 *     module [Theory].
 *     - binded indices appear in the [binded_indices] field.
 *     - [ts] contains the variable representing the block timestamp. *\)
 * type block = {
 *   ts : Term.tvar;
 *   action : Term.action;
 *   binded_indices : Term.indices;
 *   condition : Term.fact;
 *   updates : (Term.state * Term.term) list;
 *   output : Term.term } *)

type process = descr list

val subst_descr : index subst -> Term.tvar subst -> descr -> descr

(** Type of an euf axiom case.
    [e] of type [euf_case] represents the fact that the message [e.m]
    has been hashed, and the key indices were [e.eindices].
    [e.blk_descr] stores the relevant block description for future potential
    use.  *)
type euf_case = { key_indices : indices;
                  message : Term.term;
                  blk_descr : descr }

(** Type of an euf axiom rule:
    - [hash] stores the hash function name.
    - [key] stores the key considered in this rule.
    - [cases] is the list (seen as a disjunction) of cases, with all relevant
    information.*)
type euf_rule = { hash : Term.fname;
                  key : Term.name;
                  cases : euf_case list }

(** Exception thrown when the axiom syntactic side-conditions do not hold. *)
exception Bad_ssc

(** [mk_rule proc hash_fn key_n] create the euf rule associated to an given
    hash function and key in a process.
    TODO: memoisation *)
val mk_rule : process -> Term.fname -> Term.name -> euf_rule
