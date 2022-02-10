(** Module for the euf axiom application *)

(** Type of an euf axiom case schema.
    [e] of type [euf_schema] represents the fact that the message [e.message]
    has been hashed.
    [e.action] stores the relevant action for future use,
    with fresh indices where relevant (i.e. for indices other than the
    key's indices).  *)
type euf_schema = {
  action_name  : Symbols.action Symbols.t;
  action       : Action.action;
  message      : Term.message;
  key_indices  : Vars.index list;
  env          : Vars.env 
}


val pp_euf_schema : Format.formatter -> euf_schema -> unit


(** Type of a direct euf axiom case.
    [e] of type [euf_case] represents the fact that the message [e.m]
    has been hashed, and the key indices were [e.eindices]. *)
type euf_direct = {
  d_key_indices : Vars.index list;
  d_message : Term.message 
}

val pp_euf_direct : Format.formatter -> euf_direct -> unit

(** Type of an euf axiom rule:
    - [hash] stores the hash function name.
    - [key] stores the key considered in this rule.
    - [case_schemata] is the list (seen as a disjunction) of case schemata.
    - [cases_direct] is the list (seen as a disjunction) of direct cases. *)
type euf_rule = { 
  hash : Term.fname;
  key : Term.name;
  case_schemata : euf_schema list;
  cases_direct : euf_direct list 
}

val pp_euf_rule : Format.formatter -> euf_rule -> unit


(** Raises Bad_ssc if the syntactic side condition of the key is not met inside
the protocol and the messages. All occurences of the key must either be inside
the hash function, or under some public key function.*)
val key_ssc :
  ?allow_vars : bool ->
  ?messages:(Term.message list) -> ?elems:Equiv.equiv ->
  allow_functions:(Symbols.fname Symbols.t -> bool) ->
  cntxt:Constr.trace_cntxt ->
  Term.fname -> Term.name -> Tactics.ssc_error list

(*------------------------------------------------------------------*)
(** [mk_rule proc head_fn key_n] create the euf rule associated to an given head
   function and key in a process.  If drop_head is true, the message stored do
   not contain anymore the head_fn function, else they still do. *)
val mk_rule :
  ?elems:Equiv.equiv ->
  ?drop_head:bool ->
  fun_wrap_key:((Symbols.fname Symbols.t -> bool) option) ->
  allow_functions:(Symbols.fname Symbols.t -> bool) ->
  cntxt:Constr.trace_cntxt ->
  env:Vars.env -> mess:Term.message -> sign:Term.message ->
  head_fn:Term.fname -> key_n:Term.name -> key_is:Vars.index list -> euf_rule
