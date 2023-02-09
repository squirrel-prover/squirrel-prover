module Name = NameOccs.Name

type prf_param = {
  h_fn  : Symbols.fname;            (** function name *)
  h_fty : Type.ftype;               (** hash function type *)
  h_cnt : Term.term;                (** contents, i.e. hashed message *)
  h_key : Name.t;                   (** key *)
}

val prf_param : Term.term -> prf_param 

(*------------------------------------------------------------------*)
(** Build the PRF condition on one side, if the hash occurs on this side.
    Return [None] if the hash does not occurs. *)
val prf_condition_side :
  Term.proj ->
  Constr.trace_cntxt ->
  Vars.env ->
  Equiv.equiv ->
  Term.term ->
  Term.term ->
  (Term.term * Term.term) option
