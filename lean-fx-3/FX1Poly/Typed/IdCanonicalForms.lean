import FX1Poly.Typed.HasTypeDescIdElim
import FX1Poly.Typed.GrownClosedNormalClassifierShape
import FX1Poly.Typed.ConvDataCodeInjectivity
import FX1Poly.Typed.ConvCodeInjectivity

/-! # FX1Poly/Typed/IdCanonicalForms — NON-VACUOUS identity-type canonical forms (the DI-2d/5e payoff).

DI-2d typed the reflexivity VALUE `refl(x) : Id(A, x, x)` (in `HasTypeDescIdIntro`); DI-5e added the eliminator
`idJ`.  This file proves the closed-NORMAL canonical-forms theorem that makes the identity-intro engine
NON-VACUOUS: a closed normal term typed at `Id(A, left, right)` is a `refl` — across BOTH the standalone
id-intro engine AND the grown engine, unconditionally (no GrownCtxConv-5, no §5).  It completes the identity data story
(intro + elim + canon), mirroring `OptionCanonicalForms` / `ListCanonicalForms`.

## The novel rigidity route — idCode is NOT a formation-table former

Unlike `boolCode` / `optionCode` / `listCode` (which GTL-11/GTL-13 added to `typingRuleDescOf`), `gen_idCode`
is NOT in the formation table — and it CANNOT be: the formation `universeFormerOutput` rule types every
telescope child as a universe code, but `idCode`'s three children are `[typeCode, left, right]` where
`left`/`right` are TERMS (of type `typeCode`), not types.  So the within-formation-table rigidity
`formationFormersNotConvOfDistinct` (which needs BOTH formers in the table) does not apply.  Instead both
non-convertibilities use the HEAD-STABLE route directly:

  * **`Conv.idCode_not_universeCode`** — `idCode` is head-stable under reduction (`shapeStable_idCodeGeneral`,
    three children), `universeCode` is a no-step leaf, so a shared reduct carries both `gen_idCode` and
    `gen_universeCode` heads — `Generator.noConfusion`.  The three-child twin of
    `Conv.optionCode_not_universeCode`.
  * **`Conv.idCode_not_piTyCode`** — the genuinely-new pattern: BOTH `idCode` and `piTyCode` are head-stable
    (`shapeStable_idCodeGeneral` / `shapeStable_piTyCodeGeneral`), so a shared reduct carries BOTH the
    `gen_idCode` and `gen_piTyCode` heads — `Generator.noConfusion`.  (The data-canon files use
    `formationFormersNotConvOfDistinct` for this leg because their codes ARE in the table; `idCode` is not, so
    it uses the two-head-stable route — the cleaner primitive that needs no table membership at all.)

  * **`HasTypeDescPi.noClosedNormalTermAtIdType`** — the grown rule-out (CANON-1c instance): no closed-normal
    grown term inhabits an identity type.
  * **`closedNormalIdCanonicalForms` (★)** — a closed-NORMAL term typed at `Id(A, left, right)` by the id-intro
    engine OR the grown engine is a `refl`.

## SR deferral (unchanged)

These are the canonical-forms (closed-NORMAL) statements — SR-free.  Full canonicity (every closed
`t : Id(A, l, r)`, not just every normal one, reduces to a `refl`) still needs the grown master SR
(`SN-055` / GrownCtxConv-5 #842) to reduce-to-normal while preserving the classifier; that is the deferred half.

## Zero-axiom

The shipped head-stability lemmas + the universe no-step leaf + `Generator.noConfusion` (both rigidities); the
CANON-1c corollary + the rigidities (the rule-out); `subjectIsRefl` + the rule-out (the canonical forms).  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated
in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Core.StepStar FX1Poly.Universe

/-- **`Id(A, l, r) ≢ Type@_`.**  An identity type code is never convertible to a universe code: `idCode` is
head-stable under reduction (`shapeStable_idCodeGeneral`, three children), `universeCode` is a no-step leaf, so a
shared reduct carries both `gen_idCode` and `gen_universeCode` — `Generator.noConfusion`.  The three-child twin
of `Conv.optionCode_not_universeCode`. -/
theorem Conv.idCode_not_universeCode {scope : Nat}
    {typeCode left right : RawTerm scope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    (convertibility :
      Conv (idTypeCell typeCode left right) (universeCodeCell levelExpr flag)) :
    False := by
  obtain ⟨_commonReduct, leftChain, rightChain⟩ := convertibility
  obtain ⟨_typeAfter, _leftAfter, _rightAfter, leftEq, _typeStar, _leftStar, _rightStar⟩ :=
    StepStar.shapeStable_idCodeGeneral leftChain typeCode left right rfl
  have rightEq :=
    StepStar.eq_of_noStep
      (fun _reduct step => StepStar.noStep_universeCode (levelExpr, flag) step) rightChain
  rw [leftEq] at rightEq
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator rightEq :
      Generator.gen_idCode = Generator.gen_universeCode)

/-- **`Id(A, l, r) ≢ Π …`.**  An identity type code is never convertible to a dependent function type.  Unlike
the formation-table data codes (`list`/`option`), `idCode` is NOT in `typingRuleDescOf`, so this uses the
two-head-stable route directly: BOTH `idCode` and `piTyCode` are head-stable under reduction
(`shapeStable_idCodeGeneral` / `shapeStable_piTyCodeGeneral`), so a shared reduct carries BOTH `gen_idCode` and
`gen_piTyCode` — `Generator.noConfusion`. -/
theorem Conv.idCode_not_piTyCode {scope : Nat}
    {typeCode left right : RawTerm scope}
    {domain : RawTerm scope} {codomain : RawTerm (scope + 1)}
    (convertibility :
      Conv (idTypeCell typeCode left right) (piTyCodeCell domain codomain)) :
    False := by
  obtain ⟨_commonReduct, leftChain, rightChain⟩ := convertibility
  obtain ⟨_typeAfter, _leftAfter, _rightAfter, leftEq, _typeStar, _leftStar, _rightStar⟩ :=
    StepStar.shapeStable_idCodeGeneral leftChain typeCode left right rfl
  obtain ⟨_domainAfter, _codomainAfter, rightEq, _domainStar, _codomainStar⟩ :=
    StepStar.shapeStable_piTyCodeGeneral rightChain domain codomain rfl
  rw [leftEq] at rightEq
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator rightEq :
      Generator.gen_idCode = Generator.gen_piTyCode)

/-- **No closed-normal grown term inhabits an identity type.**  CANON-1c rule-out instance at `idTypeCell`:
`Id(A, l, r)` is `Conv` neither a Π-code (`idCode_not_piTyCode`) nor a universe code
(`idCode_not_universeCode`).  The grown engine types identity-FORMATION, never identity-INTRODUCTION — so it has
no `refl` value, hence no closed-normal identity inhabitant. -/
theorem HasTypeDescPi.noClosedNormalTermAtIdType {profile : PolyProfile} {subject : RawTerm 0}
    {typeCode left right : RawTerm 0}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
      (idTypeCell typeCode left right))
    (normal : RawTerm.isStepNormalForm subject) :
    False :=
  HasTypeDescPi.noClosedNormalTermAtDataClassifier typed normal
    (fun _domainCode _codomainCode convToPiCode => Conv.idCode_not_piTyCode convToPiCode)
    (fun _levelExpr _flag convToUniverseCode => Conv.idCode_not_universeCode convToUniverseCode)

/-- **★ Identity canonical forms.**  A closed-NORMAL term typed at `Id(A, left, right)` by the
identity-introduction engine OR the grown engine is a `refl` (`reflCell witness`).  The id-intro disjunct gives
it directly (`subjectIsRefl`); the grown disjunct is ruled out (`noClosedNormalTermAtIdType`).  The non-vacuous
identity canonicity — there exist typed reflexivity proofs (`reflOfUniverseCodeTyped`), and every closed-normal
identity inhabitant is one.  Stated for a GENERAL `idTypeCell typeCode left right` (the rigidities and
`subjectIsRefl` are endpoint-agnostic); `refl` itself only populates the reflexive case `left = right`. -/
theorem closedNormalIdCanonicalForms {profile : PolyProfile} {subject : RawTerm 0}
    {typeCode left right : RawTerm 0}
    (normal : RawTerm.isStepNormalForm subject)
    (typed :
      HasTypeDescIdIntro profile (TypingContext.empty : TypingContext profile 0) subject
        (idTypeCell typeCode left right) ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
        (idTypeCell typeCode left right)) :
    ∃ witness : RawTerm 0, subject = reflCell witness := by
  rcases typed with idTyped | grownTyped
  · exact idTyped.subjectIsRefl
  · exact (HasTypeDescPi.noClosedNormalTermAtIdType grownTyped normal).elim

end FX1Poly.Typed
