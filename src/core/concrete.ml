type bound = Glob | LocAsym | LocHyp | LocConc of Term.term
  (** [Glob] represent a global hypothesis/lemma
      [LocAsym] is an local asymptotic proof-term
      [LocalHyp] is when [form] come from a local hypothesis (in concrete judgement)
      [LocConc] represent a local concrete lemma*)

let bound_projs projs = function
  | LocConc t -> LocConc (Term.project projs t)
  | _ as f -> f

let bound_subst_projs (projs : (Term.proj * Term.proj) list) = function
  | LocConc t -> LocConc (Term.subst_projs projs t)
  | _ as f -> f

let bound_tsubst tsubst = function
  | LocConc t -> LocConc (Term.tsubst tsubst t)
  | _ as f -> f
