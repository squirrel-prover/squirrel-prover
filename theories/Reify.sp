(*
  This library allows term reification.

  It uses a translation of the internal representation of terms into Squirrel terms.

  This representation stays as close as possible to Squirrel internal
  representation, except that it avoids as much as possible redundant
  information.

  For example, a name `n` of type `message` is (roughly) internally
  represented as `Name { symbol: "n"; type: "message" }`, while we
  simply reify it as `Name "n"` (since its type can be easily obtained
  from the global symbol table).
  
  This file declares representations for terms, types, and systems.
*)
include "Data/List.sp".

(* ------------------------------------------------------------------- *)
(* Ident (identifiers) *)
namespace Ident.
  type t.
  op ident : string -> int -> t.
end Ident.

(* ------------------------------------------------------------------- *)
(* Tvar (type variables) *)
namespace Tvar.
  type t.
  op tvar : Ident.t -> t.
end Tvar.

(* ------------------------------------------------------------------- *)
(* Type. 

   We do not reify unification variables, since type unification is
   supposed to be done before reification can take place. *)
namespace Type.
  type t.

  op Message : t.
  op Boolean : t.
  op Index : t.
  op Timestamp : t.
  op Tbase : list string -> string -> t.
  op Tvar : Tvar.t -> t.
  op Tuple : list t -> t.
  op Fun : t -> t -> t.
end Type.

(* ------------------------------------------------------------------- *)
(* Term variables *)

(* Untyped var, used to avoid redondant information *)
namespace Var.
  type t.
  op cons : Ident.t ->  t.
end Var.

(* Typed var, used for `Find` and `Quant` *)
namespace Binder.
  type t.
  op cons : Ident.t -> Type.t ->  t.
end Binder.

(* ------------------------------------------------------------------- *)
(* Quantification and Projection *)
namespace Quant.
  type t.
  op ForAll : t.
  op Exsitential : t.
  op Seq : t.
  op Lambda : t.
end Quant.

namespace Projection.
  type t.
  op Left : t.
  op Right : t.
  op Cons : string -> t.
end Projection.

(* ------------------------------------------------------------------- *)
(* Terms *)
namespace Term.
  type t.
  
  (* a diff-term is a list of `Projection.t * Term.t` *)
  
  op Int : int -> t.
  op String : string -> t.
  op App : t -> list t -> t.
  op Fun : string -> list Type.t -> t.
  op Name : string -> list t -> t.
  op Macro : string -> list Type.t -> list t -> t -> t.
  op Action : string -> list t -> t.
  op Var : Var.t -> t.
  op Letc : Var.t -> t -> t -> t.
  op Tuple : list t -> t.
  op Proj : int -> t -> t.
  op Diff : (Projection.t * Term.t) -> t.
  op Find : list Binder.t -> t -> t -> t -> t.
  op Quant : Quant.t -> list Binder.t -> t -> t.
end Term.

(* ------------------------------------------------------------------- *)
(* Systems *)

(* System variables *)
namespace SysVar.
  type t.
  op Of_ident : Ident.t -> t.
  op Set : t.
  op Pair : t.
end SysVar.

namespace Single.
  type t.
  op make : Projection.t -> string -> t.
end Single.

(* Systems *)
namespace Sys.
  type t.
  op Var : SysVar.t -> t.
  op Any : t.
  op List : list (Projection.t * Single.t) -> t.
end Sys.

(* ------------------------------------------------------------------- *)
(* In order to unquote a reified term, we need to link variables used
   in the reify terms with corresponding values expressed in the
   current proof-context.

  For example, take the reification `Var("x")` of a variable `x`.
  Assume that, because of some proof-context manipulations, we
  instantied `x` by a term `t`.
  
  Thus, `x` no longer exists in the proof-context. To allow for such
  scenarios, we keep in an evaluation environment the map `"x" ↦ t`.
  
  An evaluation environment (of type `EvalEnv.t`, see below) maps
  reified variables to terms. It contains additional information,
  notably the (reification of) the system the reified term must be
  evaluated it. *)

(* ------------------------------------------------------------------- *)
(* A `TyDecl.t` tracks of the substitution of type variables.
   `TyDecl.make[t] (tvar "x")` means that the reified type 
    variable `"x"` in the reify term maps to `t`. *)
namespace TyDecl.
  type t.
  op make['a] : Tvar.t -> t.
end TyDecl.

(* ------------------------------------------------------------------- *)
(* `VarDecl.t` tracks of the substitution of term variables.
   `VarDecl.make (var "x") t` means that the reified term 
    variable `"x"` maps to `t`. *)
namespace VarDecl.
  type t.
  op make['a] : Var.t -> 'a -> t.
end VarDecl.

(* ------------------------------------------------------------------- *)
(* `SysDecl.t` tracks a system variable declaration.
   `SysDecl.make (sysvar "x") t` means that the reified system
   variable `"x"` is declared.*)
namespace SysDecl.
  type t.
  op make : SysVar.t -> t.
end SysDecl.

(* ------------------------------------------------------------------- *)
(* An `EvalEnv.t` is a list of `TyDecl.t`, `VarDecl.t` and `SysDecl.t`:
   - type     environement: list of `TyDecl.t`
   - variable environement: list of `VarDecl.t`
   - system   environement: list of `SysDecl.t`
 *)
namespace EvalEnv.
  type t.

  op make : list TyDecl.t -> list VarDecl.t -> list SysDecl.t -> Sys.t -> t.
end EvalEnv.

(* ------------------------------------------------------------------- *)
op hastype : (Term.t * EvalEnv.t) -> Type.t -> bool.
op Time0   : (Term.t * EvalEnv.t) -> int.
op Time1   : (Term.t * EvalEnv.t) -> int -> int.
