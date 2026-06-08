import FX1Poly.Typed.HasTypeDescListIntro
import FX1Poly.Typed.GrownClosedNormalClassifierShape
import FX1Poly.Typed.ConvDataCodeInjectivity
import FX1Poly.Typed.ConvFormationFormerRigidity

/-! # FX1Poly/Typed/ListCanonicalForms — NON-VACUOUS list canonical forms (the DI-2e payoff).

DI-2e typed the list VALUES `nil` / `cons` (in `HasTypeDescListIntro` — the first recursive data-intro).  This
file proves the closed-NORMAL canonical-forms theorem that engine makes NON-VACUOUS: a closed normal term typed
at `List(A)` is a `nil` or `cons` — across BOTH the standalone list-intro engine AND the grown engine,
unconditionally (no GrownCtxConv-5, no §5).

The grown engine contributes nothing — it has no closed-normal inhabitant of a `List` type code (it types
`List`-FORMATION, never `List`-INTRODUCTION).  This is an instance of the CANON-1c rule-out corollary
`noClosedNormalTermAtDataClassifier`, needing the two non-convertibilities for the list classifier.  Like option
(and unlike product/either, which are FLAT-table formers), `gen_listCode` is a FORMATION-table former (in
`typingRuleDescOf`, via GTL-11) — exactly like `boolCode` / `optionCode` / `sigmaTyCode` — so the rule-outs use
the FORMATION-table substrate:

  * `List(A) ≢ Π …` — the within-formation-table rigidity (`formationFormersNotConvOfDistinct`: distinct
    `typingRuleDescOf` formers are never `Conv`, `gen_listCode ≠ gen_piTyCode`).
  * `List(A) ≢ Type@_` — the head-stable-vs-leaf pattern (`List` is head-stable under reduction via
    `shapeStable_listCodeGeneral`, `universeCode` is a no-step leaf, so a shared reduct carries both heads —
    `Generator.noConfusion`).  The one-child twin of `Conv.optionCode_not_universeCode`.

  * **`Conv.listCode_not_universeCode`** — the list-vs-universe rigidity.
  * **`Conv.listCode_not_piTyCode`** — the list companion of the shipped `Conv.optionCode_not_piTyCode`, via
    `formationFormersNotConvOfDistinct`.
  * **`HasTypeDescPi.noClosedNormalTermAtListType`** — the grown rule-out (CANON-1c instance): no closed-normal
    grown term inhabits a list type.
  * **`closedNormalListCanonicalForms` (★)** — a closed-NORMAL term typed at `List(A)` by the list-intro engine
    OR the grown engine is a `nil` or `cons`.

## SR deferral (unchanged)

These are the canonical-forms (closed-NORMAL) statements — SR-free.  Full canonicity (every closed `t :
List(A)`, not just every normal one, reduces to a list value) still needs the grown master SR (`SN-055` /
GrownCtxConv-5 #842) to reduce-to-normal while preserving the classifier; that is the deferred half.

## Zero-axiom

The shipped head-stability + leaf lemmas + `Generator.noConfusion` (the universe rigidity);
`formationFormersNotConvOfDistinct` + the two `rfl` formation rows (the Π rigidity); the CANON-1c corollary +
the rigidities (the rule-out); `subjectIsListConstructor` + the rule-out (the canonical forms).  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Core.StepStar FX1Poly.Universe

/-- **`List A ≢ Type@_`.**  A list type code is never convertible to a universe code: `listCode` is head-stable
under reduction (`shapeStable_listCodeGeneral`), `universeCode` is a no-step leaf, so a shared reduct carries
both `gen_listCode` and `gen_universeCode` — `Generator.noConfusion`.  The one-child twin of
`Conv.optionCode_not_universeCode`. -/
theorem Conv.listCode_not_universeCode {scope : Nat}
    {elementType : RawTerm scope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    (convertibility :
      Conv (listTypeCell elementType) (universeCodeCell levelExpr flag)) :
    False := by
  obtain ⟨_commonReduct, leftChain, rightChain⟩ := convertibility
  obtain ⟨_elementAfter, leftEq, _elementStar⟩ :=
    StepStar.shapeStable_listCodeGeneral leftChain elementType rfl
  have rightEq :=
    StepStar.eq_of_noStep
      (fun _reduct step => StepStar.noStep_universeCode (levelExpr, flag) step) rightChain
  rw [leftEq] at rightEq
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator rightEq :
      Generator.gen_listCode = Generator.gen_universeCode)

/-- **`List A ≢ Π …`.**  A list type code is never convertible to a dependent function type — the list companion
of the shipped `Conv.optionCode_not_piTyCode`, via the within-formation-table rigidity
`formationFormersNotConvOfDistinct` (`gen_listCode ≠ gen_piTyCode`, both `typingRuleDescOf` formers). -/
theorem Conv.listCode_not_piTyCode {scope : Nat}
    {listPayload : Generator.gen_listCode.payload scope}
    {listChildren : RawTermChildren Generator.gen_listCode.binderShifts scope}
    {piPayload : Generator.gen_piTyCode.payload scope}
    {piChildren : RawTermChildren Generator.gen_piTyCode.binderShifts scope}
    (convertibility :
      Conv (.mkGen .gen_listCode listPayload listChildren)
        (.mkGen .gen_piTyCode piPayload piChildren)) :
    False :=
  Conv.formationFormersNotConvOfDistinct
    (fun headsEqual => Generator.noConfusion headsEqual)
    typingRuleDescOf_listCode typingRuleDescOf_piTyCode convertibility

/-- **No closed-normal grown term inhabits a list type.**  CANON-1c rule-out instance at `listTypeCell`:
`List(A)` is `Conv` neither a Π-code (`listCode_not_piTyCode`) nor a universe code
(`listCode_not_universeCode`).  The grown engine types list-FORMATION, never list-INTRODUCTION — so it has no
list value, hence no closed-normal list inhabitant. -/
theorem HasTypeDescPi.noClosedNormalTermAtListType {profile : PolyProfile} {subject : RawTerm 0}
    {elementType : RawTerm 0}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
      (listTypeCell elementType))
    (normal : RawTerm.isStepNormalForm subject) :
    False :=
  HasTypeDescPi.noClosedNormalTermAtDataClassifier typed normal
    (fun _domainCode _codomainCode convToPiCode => Conv.listCode_not_piTyCode convToPiCode)
    (fun _levelExpr _flag convToUniverseCode => Conv.listCode_not_universeCode convToUniverseCode)

/-- **★ List canonical forms.**  A closed-NORMAL term typed at `List(A)` by the list-introduction engine OR the
grown engine is a `nil` (`listNilCell`) or `cons` (`listConsCell`).  The list disjunct gives it directly
(`subjectIsListConstructor`); the grown disjunct is ruled out (`noClosedNormalTermAtListType`).  The non-vacuous
list canonicity — there exist typed list values (`listNilOfUniverseCodeTyped` / `listConsOfUniverseCodesTyped`),
and every closed-normal list inhabitant is one. -/
theorem closedNormalListCanonicalForms {profile : PolyProfile} {subject : RawTerm 0}
    {elementType : RawTerm 0}
    (normal : RawTerm.isStepNormalForm subject)
    (typed :
      HasTypeDescListIntro profile (TypingContext.empty : TypingContext profile 0) subject
        (listTypeCell elementType) ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
        (listTypeCell elementType)) :
    subject = listNilCell ∨
    (∃ (headValue tailList : RawTerm 0), subject = listConsCell headValue tailList) := by
  rcases typed with listTyped | grownTyped
  · exact listTyped.subjectIsListConstructor
  · exact (HasTypeDescPi.noClosedNormalTermAtListType grownTyped normal).elim

end FX1Poly.Typed
