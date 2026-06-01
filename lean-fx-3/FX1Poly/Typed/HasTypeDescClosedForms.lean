import FX1Poly.Typed.HasTypeClosedForms
import FX1Poly.Typed.HasTypeDescStronglyNormalizing

/-! # FX1Poly/Typed/HasTypeDescClosedForms
    — closed-form consequences for the description formation engine

The description formation engine `HasTypeDesc` is proven sound and complete with respect to the native
pi/sigma-formation `HasType` core.  This file transports the native closed-form facts to the description
engine side, so downstream metatheory can use the description judgment directly:

* a closed description-typed subject is an intrinsic `IsTypeDesc`;
* syntactically, a closed description-typed subject is a universe / Pi / Sigma type former; and
* its classifier is convertible to a universe code.

The scope is exactly the description formation engine.  These are not claims about the grown
`HasTypeDescPi` engine with lambda/application.

## Zero-axiom verification

Each proof is transport across the already-gated equivalence maps:
`HasTypeDesc.toHasType` and `HasType.toHasTypeDesc`, plus the native closed-form lemmas.  No recursion, no
case splitting on indexed inductives, and no use of `propext`, `Quot.sound`, `Classical`, `native_decide`,
or `omega`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- Convert a native type witness into the corresponding intrinsic description-engine type witness. -/
theorem IsType.toIsTypeDesc {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (isType : IsType profile context classifier) :
    IsTypeDesc profile context classifier := by
  obtain ⟨levelExpr, flag, typed⟩ := isType
  exact ⟨levelExpr, flag, HasType.toHasTypeDesc typed⟩

/-- Closed description-engine subjects in the formation engine are themselves description-engine types. -/
theorem HasTypeDesc.closedSubjectIsTypeDesc {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (typed : HasTypeDesc profile TypingContext.empty subject classifier) :
    IsTypeDesc profile TypingContext.empty subject :=
  (HasType.closedSubjectIsType (HasTypeDesc.toHasType typed)).toIsTypeDesc

/-- Closed-form shape for the description formation engine: a closed description-typed subject is a
universe, Pi-code, or Sigma-code cell. -/
theorem HasTypeDesc.closedSubjectIsTypeFormer {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (typed : HasTypeDesc profile TypingContext.empty subject classifier) :
    (∃ (levelExpr : LevelExpr) (flag : UniverseFlag),
        subject = universeCodeCell levelExpr flag) ∨
      (∃ (domainCode : RawTerm 0) (codomainCode : RawTerm 1),
        subject = piTyCodeCell domainCode codomainCode) ∨
      (∃ (domainCode : RawTerm 0) (codomainCode : RawTerm 1),
        subject = sigmaTyCodeCell domainCode codomainCode) :=
  HasType.closedSubjectIsTypeFormer (HasTypeDesc.toHasType typed)

/-- Consistency-facing classifier shape for the description formation engine: every closed
description-typed subject has a classifier convertible to a universe code. -/
theorem HasTypeDesc.closedClassifierConvUniverseCode {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (typed : HasTypeDesc profile TypingContext.empty subject classifier) :
    ∃ (levelExpr : LevelExpr) (flag : UniverseFlag),
      Conv classifier (universeCodeCell levelExpr flag) :=
  HasType.closedClassifierConvUniverseCode (HasTypeDesc.toHasType typed)

end FX1Poly.Typed
