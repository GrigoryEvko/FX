import FX1Poly.Typed.GrownClosedNormalClassifierShape
import FX1Poly.Typed.ConvFlatCodeInjectivity
import FX1Poly.Typed.ConvCrossTableFormerRigidity
import FX1Poly.Typed.ConvBoolCodeRigidity

/-! # FX1Poly/Typed/ProductEitherCanonicalForms — NON-VACUOUS Σ/coproduct canonical forms.

DI-2a/DI-2b typed the Σ-value `pair` and the coproduct-values `eitherInl` / `eitherInr` (in
`HasTypeDescPairIntro` / `HasTypeDescEitherIntro`).  This file proves the closed-NORMAL canonical-forms
theorems those engines make NON-VACUOUS: a closed normal term typed at `product(A, B)` is a `pair`, and at
`either(A, B)` is an `eitherInl` / `eitherInr` — across BOTH the standalone intro engine AND the grown engine,
unconditionally (no GrownCtxConv-5, no §5).

The grown engine contributes nothing — it has no closed-normal inhabitant of a `product` / `either` type code
(it types neither pairs nor injections).  This is an instance of the CANON-1c rule-out corollary
`noClosedNormalTermAtDataClassifier`, needing the two non-convertibilities for each classifier:

  * `productCode` / `eitherCode` ≢ a Π-code — the cross-table rigidity (`crossTableFormersNotConvOfDistinct`:
    a `typingRuleDescOf`-former is never `Conv` a `flatTypingRuleDescOf`-former).
  * `productCode` / `eitherCode` ≢ a universe code — the NEW rigidity this file ships, the flat-former twin of
    `Conv.boolTypeCell_not_universeCode`: the flat code is head-stable under reduction
    (`shapeStable_productCodeGeneral` / `_eitherCodeGeneral`), the universe code is a no-step leaf, so a shared
    reduct carries both heads (`Generator.noConfusion`).

  * **`Conv.productCode_not_universeCode` / `Conv.eitherCode_not_universeCode`** — the new flat-vs-universe
    rigidities.
  * **`Conv.piTyCode_not_conv_eitherCode`** — the `either` companion of the shipped
    `Conv.piTyCode_not_conv_productCode`.
  * **`HasTypeDescPi.noClosedNormalTermAtProductType` / `…AtEitherType`** — the grown rule-outs (CANON-1c
    instances): no closed-normal grown term inhabits a product / either type.
  * (The zoo-level headlines `closedNormalProductCanonicalForms` / `closedNormalEitherCanonicalForms`
    were RETIRED by NATIVE-42 — their union restatements
    `HasTypeUnion.closedNormalProductCanonicalForms` / `…EitherCanonicalForms` are the live
    canonicity statements; the rigidities and the grown rule-outs are their load-bearing substrate
    and STAY.)

## SR deferral (unchanged)

These are the canonical-forms (closed-NORMAL) statements — SR-free.  Full canonicity (every closed `t :
product(A,B)`, not just every normal one, reduces to a pair) still needs the grown master SR (`SN-055` /
GrownCtxConv-5 #842) to reduce-to-normal while preserving the classifier; that is the deferred half.

## Zero-axiom

The shipped head-stability + leaf lemmas + `Generator.noConfusion` (the rigidities); the CANON-1c corollary
`noClosedNormalTermAtDataClassifier` + the rigidities (the rule-outs); `subjectIsPair` /
`subjectIsEitherInjection` + the rule-outs (the canonical forms).  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Core.StepStar FX1Poly.Universe

/-- **`A × B ≢ Type@_`.**  A product type code is never convertible to a universe code: `productCode` is
head-stable under reduction (`shapeStable_productCodeGeneral`), `universeCode` is a no-step leaf, so a shared
reduct carries both `gen_productCode` and `gen_universeCode` — `Generator.noConfusion`.  The flat-former twin
of `Conv.boolTypeCell_not_universeCode`. -/
theorem Conv.productCode_not_universeCode {scope : Nat}
    {firstType secondType : RawTerm scope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    (convertibility :
      Conv (productTypeCell firstType secondType) (universeCodeCell levelExpr flag)) :
    False := by
  obtain ⟨_commonReduct, leftChain, rightChain⟩ := convertibility
  obtain ⟨_firstAfter, _secondAfter, leftEq, _, _⟩ :=
    StepStar.shapeStable_productCodeGeneral leftChain firstType secondType rfl
  have rightEq :=
    StepStar.eq_of_noStep
      (fun _reduct step => StepStar.noStep_universeCode (levelExpr, flag) step) rightChain
  rw [leftEq] at rightEq
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator rightEq :
      Generator.gen_productCode = Generator.gen_universeCode)

/-- **`Either A B ≢ Type@_`.**  The coproduct twin of `Conv.productCode_not_universeCode`, via
`shapeStable_eitherCodeGeneral`. -/
theorem Conv.eitherCode_not_universeCode {scope : Nat}
    {leftType rightType : RawTerm scope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    (convertibility :
      Conv (eitherTypeCell leftType rightType) (universeCodeCell levelExpr flag)) :
    False := by
  obtain ⟨_commonReduct, leftChain, rightChain⟩ := convertibility
  obtain ⟨_leftAfter, _rightAfter, leftEq, _, _⟩ :=
    StepStar.shapeStable_eitherCodeGeneral leftChain leftType rightType rfl
  have rightEq :=
    StepStar.eq_of_noStep
      (fun _reduct step => StepStar.noStep_universeCode (levelExpr, flag) step) rightChain
  rw [leftEq] at rightEq
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator rightEq :
      Generator.gen_eitherCode = Generator.gen_universeCode)

/-- **`Π … ≢ Either A B`.**  A dependent function type is never convertible to a coproduct — the `either`
companion of the shipped `Conv.piTyCode_not_conv_productCode`, via `crossTableFormersNotConvOfDistinct`. -/
theorem Conv.piTyCode_not_conv_eitherCode {scope : Nat}
    {piPayload : Generator.gen_piTyCode.payload scope}
    {piChildren : RawTermChildren Generator.gen_piTyCode.binderShifts scope}
    {eitherPayload : Generator.gen_eitherCode.payload scope}
    {eitherChildren : RawTermChildren Generator.gen_eitherCode.binderShifts scope}
    (convertibility :
      Conv (.mkGen .gen_piTyCode piPayload piChildren)
        (.mkGen .gen_eitherCode eitherPayload eitherChildren)) :
    False :=
  Conv.crossTableFormersNotConvOfDistinct
    (fun headsEqual => Generator.noConfusion headsEqual)
    typingRuleDescOf_piTyCode flatTypingRuleDescOf_eitherCode convertibility

/-- **No closed-normal grown term inhabits a product type.**  CANON-1c rule-out instance at
`productTypeCell`: `product(A, B)` is `Conv` neither a Π-code (`piTyCode_not_conv_productCode`) nor a universe
code (`productCode_not_universeCode`).  The grown engine types Σ-formation, never Σ-introduction — so it has
no pair, hence no closed-normal product inhabitant. -/
theorem HasTypeDescPi.noClosedNormalTermAtProductType {profile : PolyProfile} {subject : RawTerm 0}
    {firstType secondType : RawTerm 0}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
      (productTypeCell firstType secondType))
    (normal : RawTerm.isStepNormalForm subject) :
    False :=
  HasTypeDescPi.noClosedNormalTermAtDataClassifier typed normal
    (fun _domainCode _codomainCode convToPiCode =>
      Conv.piTyCode_not_conv_productCode convToPiCode.sym)
    (fun _levelExpr _flag convToUniverseCode => Conv.productCode_not_universeCode convToUniverseCode)

/-- **No closed-normal grown term inhabits an either type.**  The coproduct twin of
`noClosedNormalTermAtProductType`. -/
theorem HasTypeDescPi.noClosedNormalTermAtEitherType {profile : PolyProfile} {subject : RawTerm 0}
    {leftType rightType : RawTerm 0}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
      (eitherTypeCell leftType rightType))
    (normal : RawTerm.isStepNormalForm subject) :
    False :=
  HasTypeDescPi.noClosedNormalTermAtDataClassifier typed normal
    (fun _domainCode _codomainCode convToPiCode =>
      Conv.piTyCode_not_conv_eitherCode convToPiCode.sym)
    (fun _levelExpr _flag convToUniverseCode => Conv.eitherCode_not_universeCode convToUniverseCode)

end FX1Poly.Typed
