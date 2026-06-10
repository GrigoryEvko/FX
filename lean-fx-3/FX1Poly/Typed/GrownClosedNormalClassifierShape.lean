import FX1Poly.Typed.StandaloneEngineCanonicity
import FX1Poly.Typed.GrownCanonicalForms
import FX1Poly.Typed.GrownFormerClassifierConv
import FX1Poly.Typed.EmptyTypeValueInversion
import FX1Poly.Typed.ConvCodeInjectivity

/-! # FX1Poly/Typed/GrownClosedNormalClassifierShape — the grown engine inhabits ONLY functions and types
    (the positive characterization behind every data-classifier rule-out).

Last firing's `noClosedNormalTermAtBoolType` (CANON-1b) ruled out the grown engine at the `boolTypeCell`
classifier by casing `closedNormalSubjectHead` and refuting each of the six heads.  Every future data
type wants the SAME rule-out at its own classifier — so the right object is not a per-type proof but the
ONE positive characterization those proofs all factor through:

  * **`HasTypeDescPi.closedNormalClassifierIsFunctionOrType` (★)** — a CLOSED NORMAL grown-typed term's
    classifier is `Conv` a Π-code `piTyCodeCell …` OR `Conv` a universe code `universeCodeCell …`.  By
    `closedNormalSubjectHead` the subject is a λ (classifier `Conv` a Π-code, via `invertLam`) or a type
    FORMER (classifier `Conv` a universe code, via the former inversions / the head-agnostic
    `formerClassifierConvUniverseGeneric`).  This is the exact statement of the grown engine's
    expressive reach: it inhabits FUNCTION types (with λ) and UNIVERSES (with type formers), and NOTHING
    else.  The dual of `closedNormalFunctionIsLambda` / `closedNormalTypeIsFormer` (those read the
    classifier to pin the subject; this reads the subject to pin the classifier).

  * **`HasTypeDescPi.noClosedNormalTermAtDataClassifier`** — the rule-out corollary: a classifier that is
    `Conv` NEITHER a Π-code NOR a universe code has no closed-normal grown inhabitant.  Every data type
    code (`boolCode`, `emptyCode`, `sigmaTyCode`-without-introduction, …) is such a classifier, so the
    grown engine contributes NOTHING to its closed-normal inhabitants — the structural reason the
    standalone data engines carry all of data canonicity.

  * **`HasTypeDescPi.noClosedNormalTermAtSigmaType`** — the NEW Σ instance: the grown engine has no
    closed-normal inhabitant of a Σ-type (it types Σ-FORMATION `sigmaTyCode : universe` but no
    Σ-INTRODUCTION `pair : sigmaType`).  Via the corollary + `Conv.piTyCode_not_sigmaTyCode` /
    `Conv.sigmaTyCode_not_universeCode`.  The grown half of future Σ-canonicity.

  * **`closedNormalSigmaTypeUninhabited`** — combined: NO engine (data-intro / base-type / grown) types a
    closed-normal term at `sigmaTyCodeCell` — Σ-types are uninhabited across the whole current kernel (the
    data-intro classifier is `boolTypeCell`, the base-type classifier is `Type@0`, both head-distinct from
    `sigmaTyCode`; the grown disjunct is the Σ rule-out).  Honest current-state fact: Σ-values arrive only
    when a standalone Σ-introduction judgment lands (DI-2).

## Unconditional (no GrownCtxConv-5 / §5)

The classifier is read only at an ALREADY-normal subject — we invert the typing of a normal term, never
TYPE a reduction step, so no subject reduction (hence no grown context-conversion `piElim` arm, #842) is
invoked.  Exactly as `noClosedNormalTermAtBoolType` / `noClosedNormalTermAtEmptyType`.

## Zero-axiom

`closedNormalSubjectHead` (the shipped grown closed-canonical-forms recursor) + the head→shape
reconstructions + the grown inversions (`invertLam` / `invertPiTyCode` / `invertSigmaTyCode` /
`inversionUniverseCode` / `formerClassifierConvUniverseGeneric`) + the `Conv`-rigidity family +
`Generator.noConfusion`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ The grown engine inhabits only functions and types.**  A closed NORMAL grown-typed term's
classifier is `Conv` a Π-code or `Conv` a universe code.  Cases `closedNormalSubjectHead`: a λ's classifier
is `Conv` a Π-code (`invertLam`), and each of the five type-former heads has its classifier `Conv` a universe
code (`invertPiTyCode` / `invertSigmaTyCode` / `inversionUniverseCode` / the head-agnostic
`formerClassifierConvUniverseGeneric` for `listCode` / `optionCode`).  The grown engine's exact expressive
reach. -/
theorem HasTypeDescPi.closedNormalClassifierIsFunctionOrType {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject classifier)
    (normal : RawTerm.isStepNormalForm subject) :
    (∃ (domainCode : RawTerm 0) (codomainCode : RawTerm 1),
      Conv classifier (piTyCodeCell domainCode codomainCode)) ∨
    (∃ (levelExpr : LevelExpr) (flag : UniverseFlag),
      Conv classifier (universeCodeCell levelExpr flag)) := by
  rcases HasTypeDescPi.closedNormalSubjectHead typed normal
      (fun emptyIndex => emptyIndex.elim0) with
      headLam | headPi | headSigma | headUniverse | headList | headOption
  · obtain ⟨domainAnn, _body, lamEq⟩ := eq_lamCell_of_headGenerator headLam
    rw [lamEq] at typed
    obtain ⟨codomainCode, _domainLevel, _codomainLevel, _flag,
        convToPiCode, _domainTyped, _codomainTyped, _bodyTyped⟩ := HasTypeDescPi.invertLam typed
    exact Or.inl ⟨domainAnn, codomainCode, convToPiCode⟩
  · obtain ⟨_domain, _codomain, piEq⟩ := eq_piTyCodeCell_of_headGenerator headPi
    rw [piEq] at typed
    obtain ⟨_domainLevel, _codomainLevel, _flag, _domainTyped, _codomainTyped, convToUniverseCode⟩ :=
      HasTypeDescPi.invertPiTyCode typed
    exact Or.inr ⟨_, _, convToUniverseCode⟩
  · obtain ⟨_domain, _codomain, sigmaEq⟩ := eq_sigmaTyCodeCell_of_headGenerator headSigma
    rw [sigmaEq] at typed
    obtain ⟨_domainLevel, _codomainLevel, _flag, _domainTyped, _codomainTyped, convToUniverseCode⟩ :=
      HasTypeDescPi.invertSigmaTyCode typed
    exact Or.inr ⟨_, _, convToUniverseCode⟩
  · obtain ⟨_levelExpr, _flag, universeEq⟩ := eq_universeCodeCell_of_headGenerator headUniverse
    rw [universeEq] at typed
    exact Or.inr ⟨_, _, HasTypeDescPi.inversionUniverseCode typed⟩
  · obtain ⟨_element, listEq⟩ := eq_listCodeCell_of_headGenerator headList
    rw [listEq] at typed
    obtain ⟨_levels, _flag, convToUniverseCode⟩ :=
      HasTypeDescPi.formerClassifierConvUniverseGeneric typed typingRuleDescOf_listCode rfl
    exact Or.inr ⟨_, _, convToUniverseCode⟩
  · obtain ⟨_element, optionEq⟩ := eq_optionCodeCell_of_headGenerator headOption
    rw [optionEq] at typed
    obtain ⟨_levels, _flag, convToUniverseCode⟩ :=
      HasTypeDescPi.formerClassifierConvUniverseGeneric typed typingRuleDescOf_optionCode rfl
    exact Or.inr ⟨_, _, convToUniverseCode⟩

/-- **Rule-out corollary: a non-function non-type classifier has no closed-normal grown inhabitant.**  If a
classifier is `Conv` NEITHER a Π-code NOR a universe code, no closed-normal grown term is typed at it —
immediate from `closedNormalClassifierIsFunctionOrType`.  The reusable engine behind every data-classifier
rule-out (`boolCode` / `emptyCode` / `sigmaTyCode` / future data codes): supply the two non-convertibilities,
get the rule-out. -/
theorem HasTypeDescPi.noClosedNormalTermAtDataClassifier {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject classifier)
    (normal : RawTerm.isStepNormalForm subject)
    (notFunction : ∀ (domainCode : RawTerm 0) (codomainCode : RawTerm 1),
      ¬ Conv classifier (piTyCodeCell domainCode codomainCode))
    (notType : ∀ (levelExpr : LevelExpr) (flag : UniverseFlag),
      ¬ Conv classifier (universeCodeCell levelExpr flag)) :
    False := by
  rcases HasTypeDescPi.closedNormalClassifierIsFunctionOrType typed normal with
      ⟨domainCode, codomainCode, convToPiCode⟩ | ⟨levelExpr, flag, convToUniverseCode⟩
  · exact notFunction domainCode codomainCode convToPiCode
  · exact notType levelExpr flag convToUniverseCode

/-- **★ The grown engine has no closed-normal inhabitant of a Σ-type.**  A new instance of the rule-out
corollary: `sigmaTyCode` is `Conv` neither a Π-code (`Conv.piTyCode_not_sigmaTyCode`) nor a universe code
(`Conv.sigmaTyCode_not_universeCode`).  The grown engine types Σ-FORMATION (`sigmaTyCode : universe`) but no
Σ-INTRODUCTION (`pair : sigmaType`), so it inhabits no Σ-type — the grown half of future Σ-canonicity. -/
theorem HasTypeDescPi.noClosedNormalTermAtSigmaType {profile : PolyProfile} {subject : RawTerm 0}
    {sigmaDomain : RawTerm 0} {sigmaCodomain : RawTerm 1}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
      (sigmaTyCodeCell sigmaDomain sigmaCodomain))
    (normal : RawTerm.isStepNormalForm subject) :
    False :=
  HasTypeDescPi.noClosedNormalTermAtDataClassifier typed normal
    (fun _domainCode _codomainCode convToPiCode => Conv.piTyCode_not_sigmaTyCode convToPiCode.sym)
    (fun _levelExpr _flag convToUniverseCode => Conv.sigmaTyCode_not_universeCode convToUniverseCode)

/-- **Combined: no engine inhabits a Σ-type (closed-normal).**  No closed-normal term is typed at
`sigmaTyCodeCell` by `HasTypeDescDataIntro` (classifier `boolTypeCell`, head `gen_boolCode`),
`HasTypeDescBaseType` (classifier `Type@0`, head `gen_universeCode`), or `HasTypeDescPi` (the Σ rule-out).
Σ-types are uninhabited across the whole current kernel — an honest current-state fact, until a standalone
Σ-introduction judgment (DI-2) types `pair : sigmaType`.  The Σ twin of `closedNormalBoolCanonicalForms` /
`standaloneEmptyUninhabited`. -/
theorem closedNormalSigmaTypeUninhabited {profile : PolyProfile} {subject : RawTerm 0}
    {sigmaDomain : RawTerm 0} {sigmaCodomain : RawTerm 1}
    (normal : RawTerm.isStepNormalForm subject)
    (typed :
      HasTypeDescDataIntro profile (TypingContext.empty : TypingContext profile 0) subject
        (sigmaTyCodeCell sigmaDomain sigmaCodomain) ∨
      HasTypeDescBaseType profile (TypingContext.empty : TypingContext profile 0) subject
        (sigmaTyCodeCell sigmaDomain sigmaCodomain) ∨
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject
        (sigmaTyCodeCell sigmaDomain sigmaCodomain)) :
    False := by
  rcases typed with dataIntroTyped | baseTypeTyped | grownTyped
  · exact Generator.noConfusion
      (congrArg RawTerm.headGenerator dataIntroTyped.classifierIsBoolTypeCell :
        Generator.gen_sigmaTyCode = Generator.gen_boolCode)
  · exact Generator.noConfusion
      (congrArg RawTerm.headGenerator baseTypeTyped.classifierIsType0 :
        Generator.gen_sigmaTyCode = Generator.gen_universeCode)
  · exact HasTypeDescPi.noClosedNormalTermAtSigmaType grownTyped normal

end FX1Poly.Typed
