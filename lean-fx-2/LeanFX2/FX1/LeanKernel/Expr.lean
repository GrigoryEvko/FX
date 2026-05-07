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

namespace FVarId

/-- Proof-carrying structural comparison for free-variable identifiers.

`FVarId` is a single-ctor wrapper around `Name`; the comparison reduces
to `Name.eqResult` on the underlying name, then promotes the witness
through `congrArg FVarId.mk`. -/
def eqResult : (leftFvarId rightFvarId : FVarId) ->
    EqualityResult leftFvarId rightFvarId
  | FVarId.mk leftName, FVarId.mk rightName =>
      match Name.eqResult leftName rightName with
      | EqualityResult.equal nameEquality =>
          EqualityResult.equal (congrArg FVarId.mk nameEquality)
      | EqualityResult.notEqual => EqualityResult.notEqual

end FVarId

namespace MVarId

/-- Proof-carrying structural comparison for metavariable identifiers.

`MVarId` is a single-ctor wrapper around `Name`; the comparison reduces
to `Name.eqResult` on the underlying name, then promotes the witness
through `congrArg MVarId.mk`. -/
def eqResult : (leftMvarId rightMvarId : MVarId) ->
    EqualityResult leftMvarId rightMvarId
  | MVarId.mk leftName, MVarId.mk rightName =>
      match Name.eqResult leftName rightName with
      | EqualityResult.equal nameEquality =>
          EqualityResult.equal (congrArg MVarId.mk nameEquality)
      | EqualityResult.notEqual => EqualityResult.notEqual

end MVarId

namespace BinderInfo

/-- Proof-carrying structural comparison for Lean binder information.

Four-element enum: `default`, `implicit`, `strictImplicit`, `instImplicit`.
Sixteen enumerated arms keep the equation compiler from collapsing
shape-mismatch cases through wildcards (which would leak `propext`). -/
def eqResult : (leftBinder rightBinder : BinderInfo) ->
    EqualityResult leftBinder rightBinder
  | BinderInfo.default, BinderInfo.default =>
      EqualityResult.equal (Eq.refl BinderInfo.default)
  | BinderInfo.default, BinderInfo.implicit => EqualityResult.notEqual
  | BinderInfo.default, BinderInfo.strictImplicit => EqualityResult.notEqual
  | BinderInfo.default, BinderInfo.instImplicit => EqualityResult.notEqual
  | BinderInfo.implicit, BinderInfo.default => EqualityResult.notEqual
  | BinderInfo.implicit, BinderInfo.implicit =>
      EqualityResult.equal (Eq.refl BinderInfo.implicit)
  | BinderInfo.implicit, BinderInfo.strictImplicit => EqualityResult.notEqual
  | BinderInfo.implicit, BinderInfo.instImplicit => EqualityResult.notEqual
  | BinderInfo.strictImplicit, BinderInfo.default => EqualityResult.notEqual
  | BinderInfo.strictImplicit, BinderInfo.implicit => EqualityResult.notEqual
  | BinderInfo.strictImplicit, BinderInfo.strictImplicit =>
      EqualityResult.equal (Eq.refl BinderInfo.strictImplicit)
  | BinderInfo.strictImplicit, BinderInfo.instImplicit =>
      EqualityResult.notEqual
  | BinderInfo.instImplicit, BinderInfo.default => EqualityResult.notEqual
  | BinderInfo.instImplicit, BinderInfo.implicit => EqualityResult.notEqual
  | BinderInfo.instImplicit, BinderInfo.strictImplicit =>
      EqualityResult.notEqual
  | BinderInfo.instImplicit, BinderInfo.instImplicit =>
      EqualityResult.equal (Eq.refl BinderInfo.instImplicit)

end BinderInfo

namespace Literal

/-- Proof-carrying structural comparison for Lean literal payloads.

Two-element variant: `natVal` (Nat) and `strAtomVal` (Nat-encoded
string atom).  Four enumerated arms; payloads compared via
`NaturalNumber.eqResult` and lifted through `congrArg`. -/
def eqResult : (leftLiteral rightLiteral : Literal) ->
    EqualityResult leftLiteral rightLiteral
  | Literal.natVal leftValue, Literal.natVal rightValue =>
      match NaturalNumber.eqResult leftValue rightValue with
      | EqualityResult.equal valueEquality =>
          EqualityResult.equal (congrArg Literal.natVal valueEquality)
      | EqualityResult.notEqual => EqualityResult.notEqual
  | Literal.natVal _leftValue, Literal.strAtomVal _rightAtomId =>
      EqualityResult.notEqual
  | Literal.strAtomVal _leftAtomId, Literal.natVal _rightValue =>
      EqualityResult.notEqual
  | Literal.strAtomVal leftAtomId, Literal.strAtomVal rightAtomId =>
      match NaturalNumber.eqResult leftAtomId rightAtomId with
      | EqualityResult.equal atomEquality =>
          EqualityResult.equal
            (congrArg Literal.strAtomVal atomEquality)
      | EqualityResult.notEqual => EqualityResult.notEqual

end Literal

namespace Expr

/-- Copy an expression into another local-scope index.

This operation preserves the raw de Bruijn positions.  It is used only for
closed payloads whose source type already lives at scope zero, such as constant
declaration types.  A later environment well-formedness pass must reject
ill-scoped declaration payloads; this helper does not by itself prove closure. -/
def recontextualize {level sourceScope targetScope : Nat} :
    Expr level sourceScope -> Expr level targetScope
  | Expr.bvar position => Expr.bvar position
  | Expr.fvar fvarId => Expr.fvar fvarId
  | Expr.mvar mvarId => Expr.mvar mvarId
  | Expr.sort sortLevel => Expr.sort sortLevel
  | Expr.const constName levels => Expr.const constName levels
  | Expr.app functionExpr argumentExpr =>
      Expr.app
        (recontextualize functionExpr)
        (recontextualize argumentExpr)
  | Expr.lam binderName domainExpr bodyExpr binderInfo =>
      Expr.lam binderName
        (recontextualize domainExpr)
        (recontextualize
          (sourceScope := Nat.succ sourceScope)
          (targetScope := Nat.succ targetScope)
          bodyExpr)
        binderInfo
  | Expr.forallE binderName domainExpr bodyExpr binderInfo =>
      Expr.forallE binderName
        (recontextualize domainExpr)
        (recontextualize
          (sourceScope := Nat.succ sourceScope)
          (targetScope := Nat.succ targetScope)
          bodyExpr)
        binderInfo
  | Expr.letE declName typeExpr valueExpr bodyExpr nondep =>
      Expr.letE declName
        (recontextualize typeExpr)
        (recontextualize valueExpr)
        (recontextualize
          (sourceScope := Nat.succ sourceScope)
          (targetScope := Nat.succ targetScope)
          bodyExpr)
        nondep
  | Expr.lit literal => Expr.lit literal
  | Expr.mdata metadata bodyExpr =>
      Expr.mdata metadata (recontextualize bodyExpr)
  | Expr.proj structName fieldIndex targetExpr =>
      Expr.proj structName fieldIndex (recontextualize targetExpr)

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
