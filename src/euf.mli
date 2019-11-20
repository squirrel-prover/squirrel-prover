(** Module for the euf axiom application *)

open Action
open Process
open Term

val subst_descr : subst -> descr -> descr

(** Type of an euf axiom case schema.
    [e] of type [euf_schema] represents the fact that the message [e.m]
    has been hashed, and the key indices were [e.eindices].
    [e.blk_block] stores the relevant block description for future use.  *)
type euf_schema = { key_indices : Action.index list;
                    message : Term.term;
                    blk_descr : descr }


val pp_euf_schema : Format.formatter -> euf_schema -> unit


(** Type of a direct euf axiom case.
    [e] of type [euf_case] represents the fact that the message [e.m]
    has been hashed, and the key indices were [e.eindices]. *)
type euf_direct = { d_key_indices : Action.index list;
                    d_message : Term.term }

val pp_euf_direct : Format.formatter -> euf_direct -> unit

(** Type of an euf axiom rule:
    - [hash] stores the hash function name.
    - [key] stores the key considered in this rule.
    - [case_schemata] is the list (seen as a disjunction) of case schemata.
    - [cases_direct] is the list (seen as a disjunction) of direct cases. *)
type euf_rule = { hash : fname;
                  key : name;
                  case_schemata : euf_schema list;
                  cases_direct : euf_direct list }

val pp_euf_rule : Format.formatter -> euf_rule -> unit

(** Exception thrown when the axiom syntactic side-conditions do not hold. *)
exception Bad_ssc

(** [mk_rule proc hash_fn key_n] create the euf rule associated to an given
    hash function and key in a process.
    TODO: memoisation *)
val mk_rule : Vars.env ref -> term -> term -> fname -> name -> euf_rule
