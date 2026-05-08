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

namespace MDataEntry

/-- Proof-carrying structural comparison for `MDataEntry` records.

`MDataEntry` is a two-field record with `keyName : Name` and
`valueAtomId : Nat`.  Comparison reduces to `Name.eqResult` on the key
and `NaturalNumber.eqResult` on the atom id, then lifts both witnesses
through `congrArg` over the record constructor `MDataEntry.mk`. -/
def eqResult : (leftEntry rightEntry : MDataEntry) ->
    EqualityResult leftEntry rightEntry
  | { keyName := leftKey, valueAtomId := leftAtomId },
    { keyName := rightKey, valueAtomId := rightAtomId } =>
      match Name.eqResult leftKey rightKey with
      | EqualityResult.equal keyEquality =>
          match NaturalNumber.eqResult leftAtomId rightAtomId with
          | EqualityResult.equal atomEquality =>
              EqualityResult.equal
                (Eq.trans
                  (congrArg
                    (fun rewrittenKey =>
                      MDataEntry.mk rewrittenKey leftAtomId)
                    keyEquality)
                  (congrArg
                    (fun rewrittenAtom =>
                      MDataEntry.mk rightKey rewrittenAtom)
                    atomEquality))
          | EqualityResult.notEqual => EqualityResult.notEqual
      | EqualityResult.notEqual => EqualityResult.notEqual

end MDataEntry

namespace MData

/-- Proof-carrying structural comparison for `MData` records.

`MData` is a single-field record over `List MDataEntry`; comparison
delegates to `ListPayload.eqResult MDataEntry.eqResult` on the entries
list, then lifts via `congrArg MData.mk`. -/
def eqResult : (leftMetadata rightMetadata : MData) ->
    EqualityResult leftMetadata rightMetadata
  | { entries := leftEntries }, { entries := rightEntries } =>
      match
        ListPayload.eqResult MDataEntry.eqResult leftEntries rightEntries with
      | EqualityResult.equal entriesEquality =>
          EqualityResult.equal (congrArg MData.mk entriesEquality)
      | EqualityResult.notEqual => EqualityResult.notEqual

end MData

namespace Expr

/-- Canonical kernel name for the primitive natural-number type.

This is the name that the Lean-kernel typing rule for `Literal.natVal`
literals pins as the literal's type.  An environment well-formedness pass
must enforce that `natTypeName` resolves to a primitive `Nat` declaration
with the expected shape; this slice only commits to the name. -/
def natTypeName : Name := Name.str Name.anonymous Nat.zero

/-- Canonical kernel name for the primitive string type.

This is the name that the Lean-kernel typing rule for `Literal.strAtomVal`
literals pins as the literal's type.  Environment well-formedness for this
name is enforced by a later slice. -/
def stringTypeName : Name := Name.str Name.anonymous (Nat.succ Nat.zero)

/-- The canonical primitive natural-number type expression. -/
def natType {level scope : Nat} : Expr level scope :=
  Expr.const natTypeName List.nil

/-- The canonical primitive string type expression. -/
def stringType {level scope : Nat} : Expr level scope :=
  Expr.const stringTypeName List.nil

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

/-- Proof-carrying structural comparison for the 12-ctor encoded Lean
expression syntax.

Returns `EqualityResult.equal` carrying an `Eq leftExpr rightExpr`
witness when the two expressions are structurally identical, otherwise
`EqualityResult.notEqual`.  Recursion is structural on the first
argument; for binders (`lam` / `forallE` / `letE`) the body lives at
`Expr level (Nat.succ scope)` and the recursive call uses
`eqResult`'s scope polymorphism to descend uniformly.

All 144 constructor pairs (12 × 12) are enumerated explicitly to keep
Lean's match compiler from emitting `propext`-dependent equation
lemmas on the indexed `Expr level scope` inductive — wildcards or
partial patterns over indexed inductives leak `propext` through
auto-generated equation rewriters in Lean 4 v4.29.1 (per the
project's match-compiler propext recipes).

This is the load-bearing prerequisite for D8.7-EXTEND HasType.app:
the executable Lean-kernel checker needs to verify an inferred
argument type matches a Pi domain via decidable structural equality. -/
def eqResult {level : Nat} : {scope : Nat} ->
    (leftExpr rightExpr : Expr level scope) ->
      EqualityResult leftExpr rightExpr
  -- bvar (1)
  | _scope, Expr.bvar leftPosition, Expr.bvar rightPosition =>
      match NaturalNumber.eqResult leftPosition rightPosition with
      | EqualityResult.equal positionEquality =>
          EqualityResult.equal (congrArg Expr.bvar positionEquality)
      | EqualityResult.notEqual => EqualityResult.notEqual
  | _scope, Expr.bvar _, Expr.fvar _ => EqualityResult.notEqual
  | _scope, Expr.bvar _, Expr.mvar _ => EqualityResult.notEqual
  | _scope, Expr.bvar _, Expr.sort _ => EqualityResult.notEqual
  | _scope, Expr.bvar _, Expr.const _ _ => EqualityResult.notEqual
  | _scope, Expr.bvar _, Expr.app _ _ => EqualityResult.notEqual
  | _scope, Expr.bvar _, Expr.lam _ _ _ _ => EqualityResult.notEqual
  | _scope, Expr.bvar _, Expr.forallE _ _ _ _ => EqualityResult.notEqual
  | _scope, Expr.bvar _, Expr.letE _ _ _ _ _ => EqualityResult.notEqual
  | _scope, Expr.bvar _, Expr.lit _ => EqualityResult.notEqual
  | _scope, Expr.bvar _, Expr.mdata _ _ => EqualityResult.notEqual
  | _scope, Expr.bvar _, Expr.proj _ _ _ => EqualityResult.notEqual
  -- fvar (2)
  | _scope, Expr.fvar _, Expr.bvar _ => EqualityResult.notEqual
  | _scope, Expr.fvar leftFvarId, Expr.fvar rightFvarId =>
      match FVarId.eqResult leftFvarId rightFvarId with
      | EqualityResult.equal fvarEquality =>
          EqualityResult.equal (congrArg Expr.fvar fvarEquality)
      | EqualityResult.notEqual => EqualityResult.notEqual
  | _scope, Expr.fvar _, Expr.mvar _ => EqualityResult.notEqual
  | _scope, Expr.fvar _, Expr.sort _ => EqualityResult.notEqual
  | _scope, Expr.fvar _, Expr.const _ _ => EqualityResult.notEqual
  | _scope, Expr.fvar _, Expr.app _ _ => EqualityResult.notEqual
  | _scope, Expr.fvar _, Expr.lam _ _ _ _ => EqualityResult.notEqual
  | _scope, Expr.fvar _, Expr.forallE _ _ _ _ => EqualityResult.notEqual
  | _scope, Expr.fvar _, Expr.letE _ _ _ _ _ => EqualityResult.notEqual
  | _scope, Expr.fvar _, Expr.lit _ => EqualityResult.notEqual
  | _scope, Expr.fvar _, Expr.mdata _ _ => EqualityResult.notEqual
  | _scope, Expr.fvar _, Expr.proj _ _ _ => EqualityResult.notEqual
  -- mvar (3)
  | _scope, Expr.mvar _, Expr.bvar _ => EqualityResult.notEqual
  | _scope, Expr.mvar _, Expr.fvar _ => EqualityResult.notEqual
  | _scope, Expr.mvar leftMvarId, Expr.mvar rightMvarId =>
      match MVarId.eqResult leftMvarId rightMvarId with
      | EqualityResult.equal mvarEquality =>
          EqualityResult.equal (congrArg Expr.mvar mvarEquality)
      | EqualityResult.notEqual => EqualityResult.notEqual
  | _scope, Expr.mvar _, Expr.sort _ => EqualityResult.notEqual
  | _scope, Expr.mvar _, Expr.const _ _ => EqualityResult.notEqual
  | _scope, Expr.mvar _, Expr.app _ _ => EqualityResult.notEqual
  | _scope, Expr.mvar _, Expr.lam _ _ _ _ => EqualityResult.notEqual
  | _scope, Expr.mvar _, Expr.forallE _ _ _ _ => EqualityResult.notEqual
  | _scope, Expr.mvar _, Expr.letE _ _ _ _ _ => EqualityResult.notEqual
  | _scope, Expr.mvar _, Expr.lit _ => EqualityResult.notEqual
  | _scope, Expr.mvar _, Expr.mdata _ _ => EqualityResult.notEqual
  | _scope, Expr.mvar _, Expr.proj _ _ _ => EqualityResult.notEqual
  -- sort (4)
  | _scope, Expr.sort _, Expr.bvar _ => EqualityResult.notEqual
  | _scope, Expr.sort _, Expr.fvar _ => EqualityResult.notEqual
  | _scope, Expr.sort _, Expr.mvar _ => EqualityResult.notEqual
  | _scope, Expr.sort leftSortLevel, Expr.sort rightSortLevel =>
      match Level.eqResult leftSortLevel rightSortLevel with
      | EqualityResult.equal sortLevelEquality =>
          EqualityResult.equal (congrArg Expr.sort sortLevelEquality)
      | EqualityResult.notEqual => EqualityResult.notEqual
  | _scope, Expr.sort _, Expr.const _ _ => EqualityResult.notEqual
  | _scope, Expr.sort _, Expr.app _ _ => EqualityResult.notEqual
  | _scope, Expr.sort _, Expr.lam _ _ _ _ => EqualityResult.notEqual
  | _scope, Expr.sort _, Expr.forallE _ _ _ _ => EqualityResult.notEqual
  | _scope, Expr.sort _, Expr.letE _ _ _ _ _ => EqualityResult.notEqual
  | _scope, Expr.sort _, Expr.lit _ => EqualityResult.notEqual
  | _scope, Expr.sort _, Expr.mdata _ _ => EqualityResult.notEqual
  | _scope, Expr.sort _, Expr.proj _ _ _ => EqualityResult.notEqual
  -- const (5)
  | _scope, Expr.const _ _, Expr.bvar _ => EqualityResult.notEqual
  | _scope, Expr.const _ _, Expr.fvar _ => EqualityResult.notEqual
  | _scope, Expr.const _ _, Expr.mvar _ => EqualityResult.notEqual
  | _scope, Expr.const _ _, Expr.sort _ => EqualityResult.notEqual
  | _scope,
    Expr.const leftConstName leftLevels,
    Expr.const rightConstName rightLevels =>
      match Name.eqResult leftConstName rightConstName with
      | EqualityResult.equal constNameEquality =>
          match
            ListPayload.eqResult Level.eqResult leftLevels rightLevels with
          | EqualityResult.equal levelsEquality =>
              EqualityResult.equal
                (Eq.trans
                  (congrArg
                    (fun rewrittenName =>
                      Expr.const rewrittenName leftLevels)
                    constNameEquality)
                  (congrArg
                    (fun rewrittenLevels =>
                      Expr.const rightConstName rewrittenLevels)
                    levelsEquality))
          | EqualityResult.notEqual => EqualityResult.notEqual
      | EqualityResult.notEqual => EqualityResult.notEqual
  | _scope, Expr.const _ _, Expr.app _ _ => EqualityResult.notEqual
  | _scope, Expr.const _ _, Expr.lam _ _ _ _ => EqualityResult.notEqual
  | _scope, Expr.const _ _, Expr.forallE _ _ _ _ => EqualityResult.notEqual
  | _scope, Expr.const _ _, Expr.letE _ _ _ _ _ => EqualityResult.notEqual
  | _scope, Expr.const _ _, Expr.lit _ => EqualityResult.notEqual
  | _scope, Expr.const _ _, Expr.mdata _ _ => EqualityResult.notEqual
  | _scope, Expr.const _ _, Expr.proj _ _ _ => EqualityResult.notEqual
  -- app (6)
  | _scope, Expr.app _ _, Expr.bvar _ => EqualityResult.notEqual
  | _scope, Expr.app _ _, Expr.fvar _ => EqualityResult.notEqual
  | _scope, Expr.app _ _, Expr.mvar _ => EqualityResult.notEqual
  | _scope, Expr.app _ _, Expr.sort _ => EqualityResult.notEqual
  | _scope, Expr.app _ _, Expr.const _ _ => EqualityResult.notEqual
  | _scope,
    Expr.app leftFunction leftArgument,
    Expr.app rightFunction rightArgument =>
      match eqResult leftFunction rightFunction with
      | EqualityResult.equal functionEquality =>
          match eqResult leftArgument rightArgument with
          | EqualityResult.equal argumentEquality =>
              EqualityResult.equal
                (Eq.trans
                  (congrArg
                    (fun rewrittenFn => Expr.app rewrittenFn leftArgument)
                    functionEquality)
                  (congrArg
                    (fun rewrittenArg =>
                      Expr.app rightFunction rewrittenArg)
                    argumentEquality))
          | EqualityResult.notEqual => EqualityResult.notEqual
      | EqualityResult.notEqual => EqualityResult.notEqual
  | _scope, Expr.app _ _, Expr.lam _ _ _ _ => EqualityResult.notEqual
  | _scope, Expr.app _ _, Expr.forallE _ _ _ _ => EqualityResult.notEqual
  | _scope, Expr.app _ _, Expr.letE _ _ _ _ _ => EqualityResult.notEqual
  | _scope, Expr.app _ _, Expr.lit _ => EqualityResult.notEqual
  | _scope, Expr.app _ _, Expr.mdata _ _ => EqualityResult.notEqual
  | _scope, Expr.app _ _, Expr.proj _ _ _ => EqualityResult.notEqual
  -- lam (7)
  | _scope, Expr.lam _ _ _ _, Expr.bvar _ => EqualityResult.notEqual
  | _scope, Expr.lam _ _ _ _, Expr.fvar _ => EqualityResult.notEqual
  | _scope, Expr.lam _ _ _ _, Expr.mvar _ => EqualityResult.notEqual
  | _scope, Expr.lam _ _ _ _, Expr.sort _ => EqualityResult.notEqual
  | _scope, Expr.lam _ _ _ _, Expr.const _ _ => EqualityResult.notEqual
  | _scope, Expr.lam _ _ _ _, Expr.app _ _ => EqualityResult.notEqual
  | _scope,
    Expr.lam leftBinderName leftDomain leftBody leftBinderInfo,
    Expr.lam rightBinderName rightDomain rightBody rightBinderInfo =>
      match Name.eqResult leftBinderName rightBinderName with
      | EqualityResult.equal binderNameEquality =>
          match eqResult leftDomain rightDomain with
          | EqualityResult.equal domainEquality =>
              match eqResult leftBody rightBody with
              | EqualityResult.equal bodyEquality =>
                  match
                    BinderInfo.eqResult leftBinderInfo rightBinderInfo with
                  | EqualityResult.equal binderInfoEquality =>
                      EqualityResult.equal
                        (Eq.trans
                          (Eq.trans
                            (Eq.trans
                              (congrArg
                                (fun rewrittenName =>
                                  Expr.lam rewrittenName
                                    leftDomain leftBody leftBinderInfo)
                                binderNameEquality)
                              (congrArg
                                (fun rewrittenDomain =>
                                  Expr.lam rightBinderName
                                    rewrittenDomain leftBody leftBinderInfo)
                                domainEquality))
                            (congrArg
                              (fun rewrittenBody =>
                                Expr.lam rightBinderName rightDomain
                                  rewrittenBody leftBinderInfo)
                              bodyEquality))
                          (congrArg
                            (fun rewrittenBinderInfo =>
                              Expr.lam rightBinderName rightDomain
                                rightBody rewrittenBinderInfo)
                            binderInfoEquality))
                  | EqualityResult.notEqual => EqualityResult.notEqual
              | EqualityResult.notEqual => EqualityResult.notEqual
          | EqualityResult.notEqual => EqualityResult.notEqual
      | EqualityResult.notEqual => EqualityResult.notEqual
  | _scope, Expr.lam _ _ _ _, Expr.forallE _ _ _ _ => EqualityResult.notEqual
  | _scope, Expr.lam _ _ _ _, Expr.letE _ _ _ _ _ => EqualityResult.notEqual
  | _scope, Expr.lam _ _ _ _, Expr.lit _ => EqualityResult.notEqual
  | _scope, Expr.lam _ _ _ _, Expr.mdata _ _ => EqualityResult.notEqual
  | _scope, Expr.lam _ _ _ _, Expr.proj _ _ _ => EqualityResult.notEqual
  -- forallE (8)
  | _scope, Expr.forallE _ _ _ _, Expr.bvar _ => EqualityResult.notEqual
  | _scope, Expr.forallE _ _ _ _, Expr.fvar _ => EqualityResult.notEqual
  | _scope, Expr.forallE _ _ _ _, Expr.mvar _ => EqualityResult.notEqual
  | _scope, Expr.forallE _ _ _ _, Expr.sort _ => EqualityResult.notEqual
  | _scope, Expr.forallE _ _ _ _, Expr.const _ _ => EqualityResult.notEqual
  | _scope, Expr.forallE _ _ _ _, Expr.app _ _ => EqualityResult.notEqual
  | _scope, Expr.forallE _ _ _ _, Expr.lam _ _ _ _ => EqualityResult.notEqual
  | _scope,
    Expr.forallE leftBinderName leftDomain leftBody leftBinderInfo,
    Expr.forallE rightBinderName rightDomain rightBody rightBinderInfo =>
      match Name.eqResult leftBinderName rightBinderName with
      | EqualityResult.equal binderNameEquality =>
          match eqResult leftDomain rightDomain with
          | EqualityResult.equal domainEquality =>
              match eqResult leftBody rightBody with
              | EqualityResult.equal bodyEquality =>
                  match
                    BinderInfo.eqResult leftBinderInfo rightBinderInfo with
                  | EqualityResult.equal binderInfoEquality =>
                      EqualityResult.equal
                        (Eq.trans
                          (Eq.trans
                            (Eq.trans
                              (congrArg
                                (fun rewrittenName =>
                                  Expr.forallE rewrittenName
                                    leftDomain leftBody leftBinderInfo)
                                binderNameEquality)
                              (congrArg
                                (fun rewrittenDomain =>
                                  Expr.forallE rightBinderName
                                    rewrittenDomain leftBody leftBinderInfo)
                                domainEquality))
                            (congrArg
                              (fun rewrittenBody =>
                                Expr.forallE rightBinderName rightDomain
                                  rewrittenBody leftBinderInfo)
                              bodyEquality))
                          (congrArg
                            (fun rewrittenBinderInfo =>
                              Expr.forallE rightBinderName rightDomain
                                rightBody rewrittenBinderInfo)
                            binderInfoEquality))
                  | EqualityResult.notEqual => EqualityResult.notEqual
              | EqualityResult.notEqual => EqualityResult.notEqual
          | EqualityResult.notEqual => EqualityResult.notEqual
      | EqualityResult.notEqual => EqualityResult.notEqual
  | _scope, Expr.forallE _ _ _ _, Expr.letE _ _ _ _ _ =>
      EqualityResult.notEqual
  | _scope, Expr.forallE _ _ _ _, Expr.lit _ => EqualityResult.notEqual
  | _scope, Expr.forallE _ _ _ _, Expr.mdata _ _ => EqualityResult.notEqual
  | _scope, Expr.forallE _ _ _ _, Expr.proj _ _ _ => EqualityResult.notEqual
  -- letE (9)
  | _scope, Expr.letE _ _ _ _ _, Expr.bvar _ => EqualityResult.notEqual
  | _scope, Expr.letE _ _ _ _ _, Expr.fvar _ => EqualityResult.notEqual
  | _scope, Expr.letE _ _ _ _ _, Expr.mvar _ => EqualityResult.notEqual
  | _scope, Expr.letE _ _ _ _ _, Expr.sort _ => EqualityResult.notEqual
  | _scope, Expr.letE _ _ _ _ _, Expr.const _ _ => EqualityResult.notEqual
  | _scope, Expr.letE _ _ _ _ _, Expr.app _ _ => EqualityResult.notEqual
  | _scope, Expr.letE _ _ _ _ _, Expr.lam _ _ _ _ => EqualityResult.notEqual
  | _scope, Expr.letE _ _ _ _ _, Expr.forallE _ _ _ _ =>
      EqualityResult.notEqual
  | _scope,
    Expr.letE leftDeclName leftType leftValue leftBody leftNonDep,
    Expr.letE rightDeclName rightType rightValue rightBody rightNonDep =>
      match Name.eqResult leftDeclName rightDeclName with
      | EqualityResult.equal declNameEquality =>
          match eqResult leftType rightType with
          | EqualityResult.equal typeEquality =>
              match eqResult leftValue rightValue with
              | EqualityResult.equal valueEquality =>
                  match eqResult leftBody rightBody with
                  | EqualityResult.equal bodyEquality =>
                      match
                        Boolean.eqResult leftNonDep rightNonDep with
                      | EqualityResult.equal nonDepEquality =>
                          EqualityResult.equal
                            (Eq.trans
                              (Eq.trans
                                (Eq.trans
                                  (Eq.trans
                                    (congrArg
                                      (fun rewrittenName =>
                                        Expr.letE rewrittenName leftType
                                          leftValue leftBody leftNonDep)
                                      declNameEquality)
                                    (congrArg
                                      (fun rewrittenType =>
                                        Expr.letE rightDeclName rewrittenType
                                          leftValue leftBody leftNonDep)
                                      typeEquality))
                                  (congrArg
                                    (fun rewrittenValue =>
                                      Expr.letE rightDeclName rightType
                                        rewrittenValue leftBody leftNonDep)
                                    valueEquality))
                                (congrArg
                                  (fun rewrittenBody =>
                                    Expr.letE rightDeclName rightType
                                      rightValue rewrittenBody leftNonDep)
                                  bodyEquality))
                              (congrArg
                                (fun rewrittenNonDep =>
                                  Expr.letE rightDeclName rightType
                                    rightValue rightBody rewrittenNonDep)
                                nonDepEquality))
                      | EqualityResult.notEqual => EqualityResult.notEqual
                  | EqualityResult.notEqual => EqualityResult.notEqual
              | EqualityResult.notEqual => EqualityResult.notEqual
          | EqualityResult.notEqual => EqualityResult.notEqual
      | EqualityResult.notEqual => EqualityResult.notEqual
  | _scope, Expr.letE _ _ _ _ _, Expr.lit _ => EqualityResult.notEqual
  | _scope, Expr.letE _ _ _ _ _, Expr.mdata _ _ => EqualityResult.notEqual
  | _scope, Expr.letE _ _ _ _ _, Expr.proj _ _ _ => EqualityResult.notEqual
  -- lit (10)
  | _scope, Expr.lit _, Expr.bvar _ => EqualityResult.notEqual
  | _scope, Expr.lit _, Expr.fvar _ => EqualityResult.notEqual
  | _scope, Expr.lit _, Expr.mvar _ => EqualityResult.notEqual
  | _scope, Expr.lit _, Expr.sort _ => EqualityResult.notEqual
  | _scope, Expr.lit _, Expr.const _ _ => EqualityResult.notEqual
  | _scope, Expr.lit _, Expr.app _ _ => EqualityResult.notEqual
  | _scope, Expr.lit _, Expr.lam _ _ _ _ => EqualityResult.notEqual
  | _scope, Expr.lit _, Expr.forallE _ _ _ _ => EqualityResult.notEqual
  | _scope, Expr.lit _, Expr.letE _ _ _ _ _ => EqualityResult.notEqual
  | _scope, Expr.lit leftLiteral, Expr.lit rightLiteral =>
      match Literal.eqResult leftLiteral rightLiteral with
      | EqualityResult.equal literalEquality =>
          EqualityResult.equal (congrArg Expr.lit literalEquality)
      | EqualityResult.notEqual => EqualityResult.notEqual
  | _scope, Expr.lit _, Expr.mdata _ _ => EqualityResult.notEqual
  | _scope, Expr.lit _, Expr.proj _ _ _ => EqualityResult.notEqual
  -- mdata (11)
  | _scope, Expr.mdata _ _, Expr.bvar _ => EqualityResult.notEqual
  | _scope, Expr.mdata _ _, Expr.fvar _ => EqualityResult.notEqual
  | _scope, Expr.mdata _ _, Expr.mvar _ => EqualityResult.notEqual
  | _scope, Expr.mdata _ _, Expr.sort _ => EqualityResult.notEqual
  | _scope, Expr.mdata _ _, Expr.const _ _ => EqualityResult.notEqual
  | _scope, Expr.mdata _ _, Expr.app _ _ => EqualityResult.notEqual
  | _scope, Expr.mdata _ _, Expr.lam _ _ _ _ => EqualityResult.notEqual
  | _scope, Expr.mdata _ _, Expr.forallE _ _ _ _ => EqualityResult.notEqual
  | _scope, Expr.mdata _ _, Expr.letE _ _ _ _ _ => EqualityResult.notEqual
  | _scope, Expr.mdata _ _, Expr.lit _ => EqualityResult.notEqual
  | _scope,
    Expr.mdata leftMetadata leftBody,
    Expr.mdata rightMetadata rightBody =>
      match MData.eqResult leftMetadata rightMetadata with
      | EqualityResult.equal metadataEquality =>
          match eqResult leftBody rightBody with
          | EqualityResult.equal bodyEquality =>
              EqualityResult.equal
                (Eq.trans
                  (congrArg
                    (fun rewrittenMetadata =>
                      Expr.mdata rewrittenMetadata leftBody)
                    metadataEquality)
                  (congrArg
                    (fun rewrittenBody =>
                      Expr.mdata rightMetadata rewrittenBody)
                    bodyEquality))
          | EqualityResult.notEqual => EqualityResult.notEqual
      | EqualityResult.notEqual => EqualityResult.notEqual
  | _scope, Expr.mdata _ _, Expr.proj _ _ _ => EqualityResult.notEqual
  -- proj (12)
  | _scope, Expr.proj _ _ _, Expr.bvar _ => EqualityResult.notEqual
  | _scope, Expr.proj _ _ _, Expr.fvar _ => EqualityResult.notEqual
  | _scope, Expr.proj _ _ _, Expr.mvar _ => EqualityResult.notEqual
  | _scope, Expr.proj _ _ _, Expr.sort _ => EqualityResult.notEqual
  | _scope, Expr.proj _ _ _, Expr.const _ _ => EqualityResult.notEqual
  | _scope, Expr.proj _ _ _, Expr.app _ _ => EqualityResult.notEqual
  | _scope, Expr.proj _ _ _, Expr.lam _ _ _ _ => EqualityResult.notEqual
  | _scope, Expr.proj _ _ _, Expr.forallE _ _ _ _ => EqualityResult.notEqual
  | _scope, Expr.proj _ _ _, Expr.letE _ _ _ _ _ => EqualityResult.notEqual
  | _scope, Expr.proj _ _ _, Expr.lit _ => EqualityResult.notEqual
  | _scope, Expr.proj _ _ _, Expr.mdata _ _ => EqualityResult.notEqual
  | _scope,
    Expr.proj leftStructName leftFieldIndex leftTarget,
    Expr.proj rightStructName rightFieldIndex rightTarget =>
      match Name.eqResult leftStructName rightStructName with
      | EqualityResult.equal structNameEquality =>
          match
            NaturalNumber.eqResult leftFieldIndex rightFieldIndex with
          | EqualityResult.equal fieldIndexEquality =>
              match eqResult leftTarget rightTarget with
              | EqualityResult.equal targetEquality =>
                  EqualityResult.equal
                    (Eq.trans
                      (Eq.trans
                        (congrArg
                          (fun rewrittenName =>
                            Expr.proj rewrittenName
                              leftFieldIndex leftTarget)
                          structNameEquality)
                        (congrArg
                          (fun rewrittenIndex =>
                            Expr.proj rightStructName
                              rewrittenIndex leftTarget)
                          fieldIndexEquality))
                      (congrArg
                        (fun rewrittenTarget =>
                          Expr.proj rightStructName
                            rightFieldIndex rewrittenTarget)
                        targetEquality))
              | EqualityResult.notEqual => EqualityResult.notEqual
          | EqualityResult.notEqual => EqualityResult.notEqual
      | EqualityResult.notEqual => EqualityResult.notEqual

end Expr

end FX1.LeanKernel
end LeanFX2
