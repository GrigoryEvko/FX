import FX1Poly.Typed.HasTypeDescOptionIntro
import FX1Poly.Typed.HasTypeDescListIntro
import FX1Poly.Typed.HasTypeDescPairIntro
import FX1Poly.Typed.HasTypeDescEitherIntro
import FX1Poly.Typed.OptionCanonicalForms
import FX1Poly.Typed.ListCanonicalForms
import FX1Poly.Typed.ProductEitherCanonicalForms
import FX1Poly.Typed.GrownRigidityCanonicity

/-! # FX1Poly/Typed/ClosedDataCanonicity — SN-049: closed data canonicity (Option/List/Product/Either)

The arbitrary-subject closed canonicity for the remaining data types, completing the closed-data-canonicity
family (bool SN-047, nat SN-048, and now List/Option/Either/Product/Sum here).  Each is the same per-type
instantiation of the generic grown-rigidity packaging (`dataCanonicityFromGrownRigidity`) that closed nat
canonicity (`ClosedNatCanonicity`):

  * the standalone-engine canonicity (`subjectIs<Type>Constructor` — the data-intro term IS a constructor, hence
    a value, so it reduces reflexively), and
  * the type code's two shipped `Conv`-rigidities (`<code> ≢ piTyCode` rules out `lam`; `<code> ≢ universeCode`
    rules out every type former) — already proven in `OptionCanonicalForms` / `ListCanonicalForms` /
    `ProductEitherCanonicalForms` (the closed-NORMAL companions).

The grown-vacuity disjunct is DERIVED inside (`noClosedGrownTermAtDataClassifier`): the grown engine types
data-FORMATION, never data-INTRODUCTION, so it has no closed inhabitant of any data type code.

## What this ships

  * **`closedOptionCanonicalForms`** — a closed term at `option(A)` (option-intro OR grown) reduces to
    `optionNone` / `optionSome`.
  * **`closedListCanonicalForms`** — at `List(A)` reduces to `nil` / `cons`.
  * **`closedProductCanonicalForms`** — at `product(A, B)` reduces to a `pair` (the Σ/product case;
    the rigidity needs `.sym` because `productCode` is a FLAT-table former, refuted Π-side by
    `piTyCode_not_conv_productCode`).
  * **`closedEitherCanonicalForms`** — at `either(A, B)` (= Sum) reduces to `eitherInl` / `eitherInr`.
  * `*.smoke` — the non-vacuity witnesses (`optionNone` / `nil` / `pair` / `eitherInl` of universe codes are
    canonical), so none of the four statements is vacuous.

## What remains (honest, same as nat)

These range over the data-intro + grown engines — the two engines that mention a closed term at the data type
code.  A closed ELIMINATOR-headed term (`optionMatch` / `listElim` / `natElim` / …) reducing to a constructor is
the recursive eliminator-COMPUTING canonicity (#1138), needing the combined intro/elim engine — the follow-on.
Reducibility-route data canonicity is separately shipped (SN-059/064/065/066, #679/#681/#682/#684).  `Unit` is
the last SN-049 datum; its reducibility candidate is shipped (#720) and its syntactic-route instance mirrors
these once a unit type-code rule-out lands.

## Zero-axiom verification

Each is `dataCanonicityFromGrownRigidity` instantiated with the shipped `subjectIs*Constructor` (the standalone
arm) and the shipped `Conv.<code>_not_piTyCode` / `_not_universeCode` rigidities; the smokes apply it to a shipped
typed-value witness.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ Closed Option canonicity.**  A closed term typed at `option(A)` by the option-intro engine OR the grown
engine reduces to an `optionNone` or `optionSome`.  Standalone arm = `subjectIsOptionConstructor` (the value is
already normal, `StepStar.refl`); grown arm derived via `noClosedGrownTermAtDataClassifier` with the shipped
option rigidities. -/
theorem closedOptionCanonicalForms {profile : PolyProfile} {subject : RawTerm 0}
    {elementType : RawTerm 0}
    (typed :
      HasTypeDescOptionIntro profile (TypingContext.empty : TypingContext profile 0) subject
        (optionTypeCell elementType) ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
        (optionTypeCell elementType)) :
    ∃ value : RawTerm 0, StepStar subject value ∧
      (value = optionNoneCell ∨ ∃ inner : RawTerm 0, value = optionSomeCell inner) :=
  dataCanonicityFromGrownRigidity (profile := profile)
    (isValue := fun value => value = optionNoneCell ∨ ∃ inner, value = optionSomeCell inner)
    (StandaloneTyped := fun standaloneSubject =>
      HasTypeDescOptionIntro profile .empty standaloneSubject (optionTypeCell elementType))
    (fun _standaloneSubject standaloneTyped =>
      ⟨_, StepStar.refl _, standaloneTyped.subjectIsOptionConstructor⟩)
    (fun _domainCode _codomainCode convToPiCode => Conv.optionCode_not_piTyCode convToPiCode)
    (fun _levelExpr _flag convToUniverseCode => Conv.optionCode_not_universeCode convToUniverseCode)
    subject typed

/-- **Non-vacuity (option)**: `optionNone` of a universe code is canonical. -/
theorem closedOptionCanonicalForms.smoke {profile : PolyProfile} (flag : UniverseFlag) :
    ∃ value : RawTerm 0, StepStar (optionNoneCell : RawTerm 0) value ∧
      (value = optionNoneCell ∨ ∃ inner : RawTerm 0, value = optionSomeCell inner) :=
  closedOptionCanonicalForms (profile := profile)
    (Or.inl (HasTypeDescOptionIntro.optionNoneOfUniverseCodeTyped flag))

/-- **★ Closed List canonicity.**  A closed term typed at `List(A)` by the list-intro engine OR the grown engine
reduces to a `nil` or `cons`. -/
theorem closedListCanonicalForms {profile : PolyProfile} {subject : RawTerm 0}
    {elementType : RawTerm 0}
    (typed :
      HasTypeDescListIntro profile (TypingContext.empty : TypingContext profile 0) subject
        (listTypeCell elementType) ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
        (listTypeCell elementType)) :
    ∃ value : RawTerm 0, StepStar subject value ∧
      (value = listNilCell ∨
        ∃ (headValue tailList : RawTerm 0), value = listConsCell headValue tailList) :=
  dataCanonicityFromGrownRigidity (profile := profile)
    (isValue := fun value =>
      value = listNilCell ∨ ∃ (headValue tailList : RawTerm 0), value = listConsCell headValue tailList)
    (StandaloneTyped := fun standaloneSubject =>
      HasTypeDescListIntro profile .empty standaloneSubject (listTypeCell elementType))
    (fun _standaloneSubject standaloneTyped =>
      ⟨_, StepStar.refl _, standaloneTyped.subjectIsListConstructor⟩)
    (fun _domainCode _codomainCode convToPiCode => Conv.listCode_not_piTyCode convToPiCode)
    (fun _levelExpr _flag convToUniverseCode => Conv.listCode_not_universeCode convToUniverseCode)
    subject typed

/-- **Non-vacuity (list)**: `nil` of a universe code is canonical. -/
theorem closedListCanonicalForms.smoke {profile : PolyProfile} (flag : UniverseFlag) :
    ∃ value : RawTerm 0, StepStar (listNilCell : RawTerm 0) value ∧
      (value = listNilCell ∨
        ∃ (headValue tailList : RawTerm 0), value = listConsCell headValue tailList) :=
  closedListCanonicalForms (profile := profile)
    (Or.inl (HasTypeDescListIntro.listNilOfUniverseCodeTyped flag))

/-- **★ Closed Product (Σ) canonicity.**  A closed term typed at `product(A, B)` by the pair-intro engine OR the
grown engine reduces to a `pair`.  `productCode` is a FLAT-table former, so the Π rule-out uses
`piTyCode_not_conv_productCode` flipped (`.sym`). -/
theorem closedProductCanonicalForms {profile : PolyProfile} {subject : RawTerm 0}
    {firstType secondType : RawTerm 0}
    (typed :
      HasTypeDescPairIntro profile (TypingContext.empty : TypingContext profile 0) subject
        (productTypeCell firstType secondType) ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
        (productTypeCell firstType secondType)) :
    ∃ value : RawTerm 0, StepStar subject value ∧
      ∃ (firstValue secondValue : RawTerm 0), value = pairCell firstValue secondValue :=
  dataCanonicityFromGrownRigidity (profile := profile)
    (isValue := fun value =>
      ∃ (firstValue secondValue : RawTerm 0), value = pairCell firstValue secondValue)
    (StandaloneTyped := fun standaloneSubject =>
      HasTypeDescPairIntro profile .empty standaloneSubject (productTypeCell firstType secondType))
    (fun _standaloneSubject standaloneTyped =>
      ⟨_, StepStar.refl _, standaloneTyped.subjectIsPair⟩)
    (fun _domainCode _codomainCode convToPiCode => Conv.piTyCode_not_conv_productCode convToPiCode.sym)
    (fun _levelExpr _flag convToUniverseCode => Conv.productCode_not_universeCode convToUniverseCode)
    subject typed

/-- **Non-vacuity (product)**: a pair of universe codes is canonical. -/
theorem closedProductCanonicalForms.smoke {profile : PolyProfile} (flag : UniverseFlag) :
    ∃ value : RawTerm 0,
      StepStar (pairCell (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag)) value ∧
      ∃ (firstValue secondValue : RawTerm 0), value = pairCell firstValue secondValue :=
  closedProductCanonicalForms (profile := profile)
    (Or.inl (HasTypeDescPairIntro.pairOfUniverseCodesTyped flag))

/-- **★ Closed Either (Sum) canonicity.**  A closed term typed at `either(A, B)` by the either-intro engine OR
the grown engine reduces to an `eitherInl` or `eitherInr`. -/
theorem closedEitherCanonicalForms {profile : PolyProfile} {subject : RawTerm 0}
    {leftType rightType : RawTerm 0}
    (typed :
      HasTypeDescEitherIntro profile (TypingContext.empty : TypingContext profile 0) subject
        (eitherTypeCell leftType rightType) ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
        (eitherTypeCell leftType rightType)) :
    ∃ value : RawTerm 0, StepStar subject value ∧
      ((∃ inner : RawTerm 0, value = eitherInlCell inner) ∨
        (∃ inner : RawTerm 0, value = eitherInrCell inner)) :=
  dataCanonicityFromGrownRigidity (profile := profile)
    (isValue := fun value =>
      (∃ inner : RawTerm 0, value = eitherInlCell inner) ∨
        (∃ inner : RawTerm 0, value = eitherInrCell inner))
    (StandaloneTyped := fun standaloneSubject =>
      HasTypeDescEitherIntro profile .empty standaloneSubject (eitherTypeCell leftType rightType))
    (fun _standaloneSubject standaloneTyped =>
      ⟨_, StepStar.refl _, standaloneTyped.subjectIsEitherInjection⟩)
    (fun _domainCode _codomainCode convToPiCode => Conv.piTyCode_not_conv_eitherCode convToPiCode.sym)
    (fun _levelExpr _flag convToUniverseCode => Conv.eitherCode_not_universeCode convToUniverseCode)
    subject typed

/-- **Non-vacuity (either)**: `eitherInl` of a universe code is canonical. -/
theorem closedEitherCanonicalForms.smoke {profile : PolyProfile} (flag : UniverseFlag) :
    ∃ value : RawTerm 0,
      StepStar (eitherInlCell (universeCodeCell LevelExpr.lzero flag)) value ∧
      ((∃ inner : RawTerm 0, value = eitherInlCell inner) ∨
        (∃ inner : RawTerm 0, value = eitherInrCell inner)) :=
  closedEitherCanonicalForms (profile := profile)
    (Or.inl (HasTypeDescEitherIntro.eitherInlOfUniverseCodeTyped flag))

end FX1Poly.Typed
