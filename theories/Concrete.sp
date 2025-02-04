include Logic.
include Real.
include Int.
include FiniteTypes.
include Reify.

open Real.

namespace ConcreteCrypto.

op proba_fresh['a] : Real.t.
exact axiom [any] proba_fresh_leq_z['a] : z <= proba_fresh['a].

namespace ReifyOption

type t.
op some : (Term.t*EvalEnv.t) -> t.
op none : t.

end ReifyOption.

op adv_intctxt :
    (*dec*) (Term.t*EvalEnv.t)  -> (*hash*) ReifyOption.t ->
    (*c*) (Term.t*EvalEnv.t) -> (*k*) (Term.t*EvalEnv.t) ->
    (*t *) ReifyOption.t ->
    Real.t.

op adv_euf :
    (*k*) (Term.t*EvalEnv.t)  -> (*m*) (Term.t*EvalEnv.t) ->
    (*t*) (Term.t*EvalEnv.t) -> (*h*) (Term.t*EvalEnv.t) ->
    (*pk_f*) ReifyOption.t ->
    Real.t.

end ConcreteCrypto.

open ConcreteCrypto.
