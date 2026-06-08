import FX1Poly.Typed.HasTypeDescOptionIntro
import FX1Poly.Typed.GrownClosedNormalClassifierShape
import FX1Poly.Typed.ConvDataCodeInjectivity
import FX1Poly.Typed.ConvFormationFormerRigidity

/-! # FX1Poly/Typed/OptionCanonicalForms — NON-VACUOUS option canonical forms (the DI-2c payoff).

DI-2c typed the option VALUES `optionNone` / `optionSome` (in `HasTypeDescOptionIntro`); DI-5c typed and
computed the option ELIMINATOR.  This file proves the closed-NORMAL canonical-forms theorem those engines make
NON-VACUOUS: a closed normal term typed at `option(A)` is an `optionNone` or `optionSome` — across BOTH the
standalone option-intro engine AND the grown engine, unconditionally (no GCC-5, no §5).

The grown engine contributes nothing — it has no closed-normal inhabitant of an `option` type code (it types
`option`-FORMATION, never `option`-INTRODUCTION).  This is an instance of the CANON-1c rule-out corollary
`noClosedNormalTermAtDataClassifier`, needing the two non-convertibilities for the option classifier.  Unlike
the product/either canonical forms (whose codes are FLAT-table formers, so they used the flat-table rigidities),
`gen_optionCode` is a FORMATION-table former (in `typingRuleDescOf`, via GTL-13) — exactly like `boolCode` /
`sigmaTyCode` — so the rule-outs use the FORMATION-table substrate:

  * `option(A) ≢ Π …` — the within-formation-table rigidity (`formationFormersNotConvOfDistinct`: distinct
    `typingRuleDescOf` formers are never `Conv`, `gen_optionCode ≠ gen_piTyCode`).
  * `option(A) ≢ Type@_` — the NEW rigidity this file ships, the head-stable-vs-leaf pattern (`option` is
    head-stable under reduction via `shapeStable_optionCodeGeneral`, `universeCode` is a no-step leaf, so a
    shared reduct carries both heads — `Generator.noConfusion`).  The one-child twin of
    `Conv.productCode_not_universeCode`.

  * **`Conv.optionCode_not_universeCode`** — the new option-vs-universe rigidity.
  * **`Conv.optionCode_not_piTyCode`** — the option companion of the shipped `Conv.listCode_not_conv_optionCode`,
    via `formationFormersNotConvOfDistinct`.
  * **`HasTypeDescPi.noClosedNormalTermAtOptionType`** — the grown rule-out (CANON-1c instance): no closed-normal
    grown term inhabits an option type.
  * **`closedNormalOptionCanonicalForms` (★)** — a closed-NORMAL term typed at `option(A)` by the option-intro
    engine OR the grown engine is an `optionNoneCell` / `optionSomeCell`.

## SR deferral (unchanged)

These are the canonical-forms (closed-NORMAL) statements — SR-free.  Full canonicity (every closed `t :
option(A)`, not just every normal one, reduces to an option value) still needs the grown master SR (`SN-055` /
GCC-5 #842) to reduce-to-normal while preserving the classifier; that is the deferred half.

## Zero-axiom

The shipped head-stability + leaf lemmas + `Generator.noConfusion` (the universe rigidity);
`formationFormersNotConvOfDistinct` + the two `rfl` formation rows (the Π rigidity); the CANON-1c corollary +
the rigidities (the rule-out); `subjectIsOptionConstructor` + the rule-out (the canonical forms).  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Core.StepStar FX1Poly.Universe

/-- **`Option A ≢ Type@_`.**  An option type code is never convertible to a universe code: `optionCode` is
head-stable under reduction (`shapeStable_optionCodeGeneral`), `universeCode` is a no-step leaf, so a shared
reduct carries both `gen_optionCode` and `gen_universeCode` — `Generator.noConfusion`.  The one-child twin of
`Conv.productCode_not_universeCode`. -/
theorem Conv.optionCode_not_universeCode {scope : Nat}
    {elementType : RawTerm scope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    (convertibility :
      Conv (optionTypeCell elementType) (universeCodeCell levelExpr flag)) :
    False := by
  obtain ⟨_commonReduct, leftChain, rightChain⟩ := convertibility
  obtain ⟨_elementAfter, leftEq, _elementStar⟩ :=
    StepStar.shapeStable_optionCodeGeneral leftChain elementType rfl
  have rightEq :=
    StepStar.eq_of_noStep
      (fun _reduct step => StepStar.noStep_universeCode (levelExpr, flag) step) rightChain
  rw [leftEq] at rightEq
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator rightEq :
      Generator.gen_optionCode = Generator.gen_universeCode)

/-- **`Option A ≢ Π …`.**  An option type code is never convertible to a dependent function type — the option
companion of the shipped `Conv.listCode_not_conv_optionCode`, via the within-formation-table rigidity
`formationFormersNotConvOfDistinct` (`gen_optionCode ≠ gen_piTyCode`, both `typingRuleDescOf` formers). -/
theorem Conv.optionCode_not_piTyCode {scope : Nat}
    {optionPayload : Generator.gen_optionCode.payload scope}
    {optionChildren : RawTermChildren Generator.gen_optionCode.binderShifts scope}
    {piPayload : Generator.gen_piTyCode.payload scope}
    {piChildren : RawTermChildren Generator.gen_piTyCode.binderShifts scope}
    (convertibility :
      Conv (.mkGen .gen_optionCode optionPayload optionChildren)
        (.mkGen .gen_piTyCode piPayload piChildren)) :
    False :=
  Conv.formationFormersNotConvOfDistinct
    (fun headsEqual => Generator.noConfusion headsEqual)
    typingRuleDescOf_optionCode typingRuleDescOf_piTyCode convertibility

/-- **No closed-normal grown term inhabits an option type.**  CANON-1c rule-out instance at `optionTypeCell`:
`option(A)` is `Conv` neither a Π-code (`optionCode_not_piTyCode`) nor a universe code
(`optionCode_not_universeCode`).  The grown engine types option-FORMATION, never option-INTRODUCTION — so it has
no option value, hence no closed-normal option inhabitant. -/
theorem HasTypeDescPi.noClosedNormalTermAtOptionType {profile : PolyProfile} {subject : RawTerm 0}
    {elementType : RawTerm 0}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
      (optionTypeCell elementType))
    (normal : RawTerm.isStepNormalForm subject) :
    False :=
  HasTypeDescPi.noClosedNormalTermAtDataClassifier typed normal
    (fun _domainCode _codomainCode convToPiCode => Conv.optionCode_not_piTyCode convToPiCode)
    (fun _levelExpr _flag convToUniverseCode => Conv.optionCode_not_universeCode convToUniverseCode)

/-- **★ Option canonical forms.**  A closed-NORMAL term typed at `option(A)` by the option-introduction engine
OR the grown engine is an `optionNoneCell` or `optionSomeCell`.  The option disjunct gives it directly
(`subjectIsOptionConstructor`); the grown disjunct is ruled out (`noClosedNormalTermAtOptionType`).  The
non-vacuous option canonicity — there exist typed option values (`optionNoneOfUniverseCodeTyped` /
`optionSomeOfUniverseCodeTyped`), and every closed-normal option inhabitant is one. -/
theorem closedNormalOptionCanonicalForms {profile : PolyProfile} {subject : RawTerm 0}
    {elementType : RawTerm 0}
    (normal : RawTerm.isStepNormalForm subject)
    (typed :
      HasTypeDescOptionIntro profile (TypingContext.empty : TypingContext profile 0) subject
        (optionTypeCell elementType) ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
        (optionTypeCell elementType)) :
    subject = optionNoneCell ∨ (∃ value : RawTerm 0, subject = optionSomeCell value) := by
  rcases typed with optionTyped | grownTyped
  · exact optionTyped.subjectIsOptionConstructor
  · exact (HasTypeDescPi.noClosedNormalTermAtOptionType grownTyped normal).elim

end FX1Poly.Typed
