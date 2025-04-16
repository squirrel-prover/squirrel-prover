open Utils

(* DEPRECATED, should no longer be used *)
(** Module for the euf axiom application *)
(*------------------------------------------------------------------*)
(** Type of an euf axiom case schema.
    [e] of type [euf_schema] represents the fact that the message [e.message]
    has been hashed.
    [e.action] stores the relevant action for future use,
    with fresh indices where relevant (i.e. for indices other than the
    key's indices).  *)
type euf_schema = {
  rec_arg      : Term.term;
  message      : Term.term;
  key_indices  : Term.terms;
  env          : Vars.env 
}


val pp_euf_schema : euf_schema formatter

(*------------------------------------------------------------------*)
(** Type of a direct euf axiom case.
    [e] of type [euf_case] represents the fact that the message [e.m]
    has been hashed, and the key indices were [e.eindices]. *)
type euf_direct = {
  d_key_indices : Term.terms;
  d_message : Term.term 
}

val pp_euf_direct : euf_direct formatter

(*------------------------------------------------------------------*)
(** Type of an euf axiom rule:
    - [hash] stores the hash function name.
    - [key] stores the key considered in this rule.
    - [case_schemata] is the list (seen as a disjunction) of case schemata.
    - [cases_direct] is the list (seen as a disjunction) of direct cases. *)
type euf_rule = { 
  hash : Symbols.fname;
  key : Symbols.name * Term.terms ; (* k(t1, ..., tn) *)
  case_schemata : euf_schema list;
  cases_direct : euf_direct list 
}

val pp_euf_rule : euf_rule formatter

(*------------------------------------------------------------------*)
(** Check the syntactic side conditions of the key in the protocol and
    the messages.
    When [global] is true, also checks in global macros. *)
val key_ssc :
  ?messages:(Term.term list) ->
  ?elems:Equiv.equiv ->
  allow_functions:(Symbols.fname -> bool) ->
  context:ProofContext.t ->
  Symbols.fname -> Symbols.name -> Tactics.ssc_error list

(*------------------------------------------------------------------*)
(** [mk_rule proc head_fn key_n] create the euf rule associated to an given head
   function and key in a process.  If drop_head is true, the message stored do
   not contain anymore the head_fn function, else they still do. *)
val mk_rule :
  elems:Equiv.equiv ->
  drop_head:bool ->
  fun_wrap_key:((Symbols.fname -> bool) option) ->
  context:ProofContext.t ->
  mess:Term.term -> sign:Term.term ->
  head_fn:Symbols.fname -> key_n:Symbols.name -> key_is:Term.terms -> euf_rule
