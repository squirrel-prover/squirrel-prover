type bound = 
  | Glob                 (** a global hypothesis/lemma *)
  | LocAsym              (** a local asymptotic proof-term *)
  | LocHyp               (** when [form] comes from a local hypothesis (in a concrete judgement) *)
  | LocConc of Term.term (** a local concrete lemma *)


let bound_projs projs = function
  | LocConc t -> LocConc (Term.project projs t)
  | _ as f -> f

let bound_subst_projs (projs : (Term.proj * Term.proj) list) = function
  | LocConc t -> LocConc (Term.subst_projs projs t)
  | _ as f -> f

let bound_tsubst tsubst = function
  | LocConc t -> LocConc (Term.tsubst tsubst t)
  | _ as f -> f
