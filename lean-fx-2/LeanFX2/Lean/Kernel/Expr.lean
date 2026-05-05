import LeanFX2.Lean.Kernel.Name
import LeanFX2.Lean.Kernel.Level

/-! # Lean/Kernel/Expr

Lean kernel expressions.

## Deliverable

This module encodes the twelve kernel expression constructors used by Lean 4.
The encoding strengthens bound variables from raw `Nat` indices to
`Fin scope`, making malformed de Bruijn references unrepresentable in this
mechanization.
-/

namespace LeanFX2
namespace LeanKernel

/-- Free-variable identifiers in the encoded Lean kernel. -/
inductive FVarId : Type
  | mk (name : Name) : FVarId
  deriving DecidableEq, Repr

/-- Metavariable identifiers in the encoded Lean kernel. -/
inductive MVarId : Type
  | mk (name : Name) : MVarId
  deriving DecidableEq, Repr

/-- Lean binder information. -/
inductive BinderInfo : Type
  | default : BinderInfo
  | implicit : BinderInfo
  | strictImplicit : BinderInfo
  | instImplicit : BinderInfo
  deriving DecidableEq, Repr

/-- Literal payloads accepted by Lean expressions. -/
inductive Literal : Type
  | natVal (value : Nat) : Literal
  | strVal (value : String) : Literal
  deriving DecidableEq, Repr

/-- Minimal metadata representation for `Expr.mdata`.

Lean's runtime metadata map is richer; this syntax layer only needs a
deterministic, inspectable payload so metadata nodes can be represented and
ignored by later kernel rules. -/
structure MData : Type where
  entries : List (Name × String)
  deriving DecidableEq, Repr

/-- Lean kernel expression syntax, indexed by universe-level budget and local
bound-variable scope.

The constructor set matches Lean's expression kind enum:
`bvar`, `fvar`, `mvar`, `sort`, `const`, `app`, `lam`, `forallE`, `letE`,
`lit`, `mdata`, and `proj`. -/
inductive Expr : Nat → Nat → Type
  | bvar {level scope : Nat}
      (position : Fin scope) : Expr level scope
  | fvar {level scope : Nat}
      (fvarId : FVarId) : Expr level scope
  | mvar {level scope : Nat}
      (mvarId : MVarId) : Expr level scope
  | sort {level scope : Nat}
      (sortLevel : Level) : Expr level scope
  | const {level scope : Nat}
      (constName : Name)
      (levels : List Level) : Expr level scope
  | app {level scope : Nat}
      (functionExpr argumentExpr : Expr level scope) : Expr level scope
  | lam {level scope : Nat}
      (binderName : Name)
      (domainExpr : Expr level scope)
      (bodyExpr : Expr level (scope + 1))
      (binderInfo : BinderInfo) : Expr level scope
  | forallE {level scope : Nat}
      (binderName : Name)
      (domainExpr : Expr level scope)
      (bodyExpr : Expr level (scope + 1))
      (binderInfo : BinderInfo) : Expr level scope
  | letE {level scope : Nat}
      (declName : Name)
      (typeExpr valueExpr : Expr level scope)
      (bodyExpr : Expr level (scope + 1))
      (nondep : Bool) : Expr level scope
  | lit {level scope : Nat}
      (literal : Literal) : Expr level scope
  | mdata {level scope : Nat}
      (metadata : MData)
      (bodyExpr : Expr level scope) : Expr level scope
  | proj {level scope : Nat}
      (structName : Name)
      (fieldIndex : Nat)
      (targetExpr : Expr level scope) : Expr level scope

namespace Expr

/-- Count expression nodes.  This is a structural sanity check used by early
kernel tooling before substitution and typing are populated. -/
def nodeCount {level : Nat} : ∀ {scope : Nat}, Expr level scope → Nat
  | _, bvar _position => 1
  | _, fvar _fvarId => 1
  | _, mvar _mvarId => 1
  | _, sort _sortLevel => 1
  | _, const _constName _levels => 1
  | _, app functionExpr argumentExpr =>
      1 + nodeCount functionExpr + nodeCount argumentExpr
  | _, lam _binderName domainExpr bodyExpr _binderInfo =>
      1 + nodeCount domainExpr + nodeCount bodyExpr
  | _, forallE _binderName domainExpr bodyExpr _binderInfo =>
      1 + nodeCount domainExpr + nodeCount bodyExpr
  | _, letE _declName typeExpr valueExpr bodyExpr _nondep =>
      1 + nodeCount typeExpr + nodeCount valueExpr + nodeCount bodyExpr
  | _, lit _literal => 1
  | _, mdata _metadata bodyExpr =>
      1 + nodeCount bodyExpr
  | _, proj _structName _fieldIndex targetExpr =>
      1 + nodeCount targetExpr

/-- Applications have at least three nodes when both sides are atomic. -/
theorem nodeCount_app {level scope : Nat}
    (functionExpr argumentExpr : Expr level scope) :
    nodeCount (app functionExpr argumentExpr) =
      1 + nodeCount functionExpr + nodeCount argumentExpr := rfl

/-- Metadata contributes one wrapper node. -/
theorem nodeCount_mdata {level scope : Nat}
    (metadata : MData)
    (bodyExpr : Expr level scope) :
    nodeCount (mdata metadata bodyExpr) = 1 + nodeCount bodyExpr := rfl

end Expr

end LeanKernel
end LeanFX2
