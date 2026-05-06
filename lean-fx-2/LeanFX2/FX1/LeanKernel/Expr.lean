prelude
import LeanFX2.FX1.LeanKernel.Level

/-! # FX1/LeanKernel/Expr

Lean kernel expressions.

## Deliverable

This module encodes the twelve kernel expression constructors used by Lean 4.
Bound variables use Lean's actual `Nat` representation; scope validity is a
typing/checker obligation rather than a dependency on host `Fin` helper lemmas.
-/

namespace LeanFX2
namespace FX1.LeanKernel

/-- Free-variable identifiers in the encoded Lean kernel. -/
inductive FVarId : Type
  | mk (name : Name) : FVarId

/-- Metavariable identifiers in the encoded Lean kernel. -/
inductive MVarId : Type
  | mk (name : Name) : MVarId

/-- Lean binder information. -/
inductive BinderInfo : Type
  | default : BinderInfo
  | implicit : BinderInfo
  | strictImplicit : BinderInfo
  | instImplicit : BinderInfo

/-- Literal payloads accepted by Lean expressions. -/
inductive Literal : Type
  | natVal (value : Nat) : Literal
  | strAtomVal (atomId : Nat) : Literal

/-- One metadata entry.  Payloads are atom ids, not host strings. -/
structure MDataEntry : Type where
  keyName : Name
  valueAtomId : Nat

/-- Minimal metadata representation for `Expr.mdata`.

Lean's runtime metadata map is richer; this syntax layer only needs a
deterministic, inspectable payload so metadata nodes can be represented and
ignored by later kernel rules. -/
structure MData : Type where
  entries : List MDataEntry

/-- Lean kernel expression syntax, indexed by universe-level budget and local
bound-variable scope.

The constructor set matches Lean's expression kind enum:
`bvar`, `fvar`, `mvar`, `sort`, `const`, `app`, `lam`, `forallE`, `letE`,
`lit`, `mdata`, and `proj`. -/
inductive Expr : Nat -> Nat -> Type
  | bvar {level scope : Nat}
      (position : Nat) : Expr level scope
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
      (bodyExpr : Expr level (Nat.succ scope))
      (binderInfo : BinderInfo) : Expr level scope
  | forallE {level scope : Nat}
      (binderName : Name)
      (domainExpr : Expr level scope)
      (bodyExpr : Expr level (Nat.succ scope))
      (binderInfo : BinderInfo) : Expr level scope
  | letE {level scope : Nat}
      (declName : Name)
      (typeExpr valueExpr : Expr level scope)
      (bodyExpr : Expr level (Nat.succ scope))
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
def nodeCount {level : Nat} : {scope : Nat} -> Expr level scope -> Nat
  | _, Expr.bvar _position => 1
  | _, Expr.fvar _fvarId => 1
  | _, Expr.mvar _mvarId => 1
  | _, Expr.sort _sortLevel => 1
  | _, Expr.const _constName _levels => 1
  | _, Expr.app functionExpr argumentExpr =>
      Nat.succ (Nat.add (nodeCount functionExpr) (nodeCount argumentExpr))
  | _, Expr.lam _binderName domainExpr bodyExpr _binderInfo =>
      Nat.succ (Nat.add (nodeCount domainExpr) (nodeCount bodyExpr))
  | _, Expr.forallE _binderName domainExpr bodyExpr _binderInfo =>
      Nat.succ (Nat.add (nodeCount domainExpr) (nodeCount bodyExpr))
  | _, Expr.letE _declName typeExpr valueExpr bodyExpr _nondep =>
      Nat.succ
        (Nat.add
          (nodeCount typeExpr)
          (Nat.add (nodeCount valueExpr) (nodeCount bodyExpr)))
  | _, Expr.lit _literal => 1
  | _, Expr.mdata _metadata bodyExpr =>
      Nat.succ (nodeCount bodyExpr)
  | _, Expr.proj _structName _fieldIndex targetExpr =>
      Nat.succ (nodeCount targetExpr)

/-- Applications have at least three nodes when both sides are atomic. -/
theorem nodeCount_app {level scope : Nat}
    (functionExpr argumentExpr : Expr level scope) :
    Eq
      (nodeCount (Expr.app functionExpr argumentExpr))
      (Nat.succ (Nat.add (nodeCount functionExpr) (nodeCount argumentExpr))) :=
  Eq.refl
    (Nat.succ (Nat.add (nodeCount functionExpr) (nodeCount argumentExpr)))

/-- Metadata contributes one wrapper node. -/
theorem nodeCount_mdata {level scope : Nat}
    (metadata : MData)
    (bodyExpr : Expr level scope) :
    Eq
      (nodeCount (Expr.mdata metadata bodyExpr))
      (Nat.succ (nodeCount bodyExpr)) :=
  Eq.refl (Nat.succ (nodeCount bodyExpr))

end Expr

end FX1.LeanKernel
end LeanFX2
