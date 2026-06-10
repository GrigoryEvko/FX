import FX1Poly.Typed.TypeAxisObligation
import FX1Poly.Modal.GradedEvaluation
import FX1Poly.Modal.GradedNormalizerValue
import FX1Poly.Modal.GradedReductionConfluence

/-! # FX1Poly/Typed/UsageAxisObligation
    — the usage (linearity) AxisObligation: an honest PARTIAL ledger + a fully-DISCHARGED sconing witness (SN-105, #608)

The second concrete `AxisObligation`, and the first with a genuinely PARTIAL capability ledger —
demonstrating the ledger discriminates rather than rubber-stamps.  The usage dimension is the
load-bearing graded dimension (separation logic IS the usage grade, design §6.4); its shipped
metatheory lives over the graded λ-calculus (`GradedLambda` / `HasGradeOver fxUsageSemiring`, the
corrected Wood-Atkey Lam rule via context division):

  * `usageAxisCapabilities` — FIVE fields `.available`, each backed: canonicity
    (`closedReducesToLam` — closed well-graded terms reduce to λ-values), normalization (the graded
    normalizer + its soundness laws), subject reduction (`hasGradeOver_reducesStarPreservation`),
    confluence (graded Newman over graded SN), strong normalization
    (`HasGradeOver.stronglyNormalizing` — the erasure transfer, NO per-dimension SN re-proof).
    THREE fields `.unavailable`, each honestly pinned: parametricity (no usage-indexed relational
    interpretation is shipped; `DIM-FUNCTORIAL` is the projection statement, a different theorem),
    decidable conversion (derivable by normalize-and-compare over graded SN but NOT shipped),
    decidable typechecking (no `HasGradeOver` decision procedure is shipped — the inversion lemmas
    exist, the decider does not).
  * `fxUsageAxisObligation` — axis id `.multiModal` (the §6 graded dimensions are MTT-style
    modalities), Fire-Triangle restriction `some .substitution` — the honest semantic restriction:
    linearity restricts SUBSTITUTION (no contraction/weakening; a linear variable cannot be
    duplicated by a substitution), exactly the leg the ∂CBPV Fire-Triangle analysis assigns to
    substructural dimensions.  Precedents: Girard / McBride / Atkey / Wood-Atkey.
  * ★ `usageSconingWitness` — **the usage sconing witness with a DISCHARGED fundamental**: the
    computability predicate pairs strong normalization with reaches-a-λ-value over the closed
    well-graded terms; BOTH the fundamental and the extraction are theorems (not hypotheses) —
    stronger than the RawTerm data scones, whose fundamentals await their engines.  The fundamental
    respects the grade arithmetic by construction: it consumes `HasGradeOver` derivations built by
    the corrected Wood-Atkey rules over `fxUsageSemiring` (`1 + 1 = ω`, pinned below), the system
    that REJECTS the Atkey-2018 broken Lam (the §27.2 corpus row).
  * `usageGradeArithmetic_oneAddOne` — the load-bearing semiring fact `1 + 1 = ω` (using a linear
    variable twice makes it unrestricted), pinned `rfl` — the arithmetic the witness's fundamental
    respects.
  * `usageAxis_meetWithTypeAxis` — composition breadcrumb for SN-108: meeting the usage ledger
    against the discharged type axis preserves it exactly (the SN-103 meet-identity applied).

## Honest scope boundary

The usage metatheory is over the GRADED λ-CALCULUS (`GradedLambda`, simple types + grade vectors) —
the §6 usage dimension's mechanization substrate — NOT over the 198-generator `RawTerm` kernel; the
composition with the dependent type axis is by grade ERASURE (`HasGradeOver.erase`, the DIM2-7
no-cascade ledger), not by a joint judgment.  The three `.unavailable` fields are real gaps, each
with a recorded route (usage-indexed relations; normalize-and-compare decider; grade inference).

## Zero-axiom verification

A capabilities literal, an obligation record, five backed-flip conjunctions by direct application of
the shipped graded results, three honest-absence `rfl` pins, the witness structure with discharged
fields, and arithmetic `rfl` pins.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Tier0 FX1Poly.Modal

/-- **The usage-axis capability ledger** — honestly PARTIAL: five capabilities backed by the shipped
graded metatheory, three genuinely absent (parametricity, decidable conversion, decidable
typechecking). -/
def usageAxisCapabilities : MetatheoreticCapabilities where
  canonicityStatus := .available
  normalizationStatus := .available
  parametricityStatus := .unavailable
  subjectReductionStatus := .available
  confluenceStatus := .available
  strongNormalizationStatus := .available
  decidableConversionStatus := .unavailable
  decidableTypecheckingStatus := .unavailable

/-- The usage ledger is strictly between bottom and top — the first PROPER capability instance,
witnessing that the ledger discriminates. -/
theorem usageAxisCapabilities_isProper :
    usageAxisCapabilities ≠ MetatheoreticCapabilities.top
      ∧ usageAxisCapabilities ≠ MetatheoreticCapabilities.bot :=
  ⟨fun absurdEq =>
      (nomatch congrArg MetatheoreticCapabilities.parametricityStatus absurdEq),
   fun absurdEq =>
      (nomatch congrArg MetatheoreticCapabilities.canonicityStatus absurdEq)⟩

/-- **The usage (linearity) axis obligation**: the §6 usage dimension over the graded λ-calculus,
on the multi-modal axis (graded dimensions are MTT-style modalities), with the honest Fire-Triangle
restriction `some .substitution` — linearity restricts substitution (no contraction/weakening). -/
def fxUsageAxisObligation : AxisObligation where
  axisName := "FX usage (linearity) dimension over the graded lambda calculus"
  axisId := .multiModal
  fireTriangleRestriction := some .substitution
  capabilities := usageAxisCapabilities
  estimatedLinesOfCode := 0
  precedents :=
    [⟨"J.-Y. Girard", "Linear logic", none, 1987⟩,
     ⟨"C. McBride", "I Got Plenty o' Nuttin'", none, 2016⟩,
     ⟨"R. Atkey", "Syntax and Semantics of Quantitative Type Theory", none, 2018⟩,
     ⟨"J. Wood, R. Atkey", "A Framework for Substructural Type Systems", none, 2022⟩]

/-- **The load-bearing grade arithmetic, pinned**: using a linear variable twice makes it
unrestricted (`1 + 1 = ω`) — the §6.1 usage-semiring fact the witness's fundamental respects (a
context split that duplicates a linear binding lands at `ω`, never back at `1`). -/
theorem usageGradeArithmetic_oneAddOne :
    fxUsageSemiring.add fxUsageSemiring.one fxUsageSemiring.one = UsageGrade.omega := rfl

/-- Sequential use multiplies: `1 * 1 = 1` — a single linear use through a single linear consumer
stays linear. -/
theorem usageGradeArithmetic_oneMulOne :
    fxUsageSemiring.mul fxUsageSemiring.one fxUsageSemiring.one = UsageGrade.one := rfl

/-- **Backed flip (strong normalization)**: every well-graded usage term — over ANY context — is
strongly normalizing, by the erasure transfer (`HasGradeOver.stronglyNormalizing`): the type-axis
SN transfers through grade erasure with no per-dimension re-proof (the DIM2-5 de-risk). -/
theorem usageAxis_strongNormalization_isBacked :
    fxUsageAxisObligation.capabilities.strongNormalizationStatus = .available
      ∧ (∀ {typeContext : List (GTypeOver fxUsageSemiring)}
          {grades : GradeVectorOver fxUsageSemiring} {term : GradedLambda}
          {resultType : GTypeOver fxUsageSemiring},
          HasGradeOver fxUsageSemiring typeContext grades term resultType →
          GradedLambda.IsStronglyNormalizing term) :=
  ⟨rfl, fun typed => typed.stronglyNormalizing⟩

/-- **Backed flip (canonicity)**: every CLOSED well-graded usage term reduces to a λ-value
(`closedReducesToLam` at the lawful usage semiring). -/
theorem usageAxis_canonicity_isBacked :
    fxUsageAxisObligation.capabilities.canonicityStatus = .available
      ∧ (∀ {grades : GradeVectorOver fxUsageSemiring} {term : GradedLambda}
          {resultType : GTypeOver fxUsageSemiring},
          HasGradeOver fxUsageSemiring [] grades term resultType →
          ∃ body, GradedLambda.ReducesStar term (.lam body)) :=
  ⟨rfl, fun typed => closedReducesToLam fxUsageSemiring_isLawful typed⟩

/-- **Backed flip (normalization)**: every well-graded usage term reaches a normal form — the
graded normalizer over the transferred SN, with its two shipped soundness laws. -/
theorem usageAxis_normalization_isBacked :
    fxUsageAxisObligation.capabilities.normalizationStatus = .available
      ∧ (∀ {typeContext : List (GTypeOver fxUsageSemiring)}
          {grades : GradeVectorOver fxUsageSemiring} {term : GradedLambda}
          {resultType : GTypeOver fxUsageSemiring},
          HasGradeOver fxUsageSemiring typeContext grades term resultType →
          ∃ normalForm : GradedLambda,
            GradedLambda.ReducesStar term normalForm
              ∧ GradedLambda.IsNormalForm normalForm) :=
  ⟨rfl, fun typed =>
    have isTermNormalizing := typed.stronglyNormalizing
    ⟨GradedLambda.normalize _ isTermNormalizing,
     GradedLambda.normalize_reducesStar _ isTermNormalizing,
     GradedLambda.normalize_isNormalForm _ isTermNormalizing⟩⟩

/-- **Backed flip (subject reduction)**: graded typing — grades INCLUDED — is preserved along
arbitrary reduction sequences (`hasGradeOver_reducesStarPreservation` at the lawful usage
semiring). -/
theorem usageAxis_subjectReduction_isBacked :
    fxUsageAxisObligation.capabilities.subjectReductionStatus = .available
      ∧ (∀ {typeContext : List (GTypeOver fxUsageSemiring)} {term reduct : GradedLambda},
          GradedLambda.ReducesStar term reduct →
          ∀ {grades : GradeVectorOver fxUsageSemiring}
            {resultType : GTypeOver fxUsageSemiring},
            HasGradeOver fxUsageSemiring typeContext grades term resultType →
            HasGradeOver fxUsageSemiring typeContext grades reduct resultType) :=
  ⟨rfl, fun {typeContext} {term} {reduct} star {grades} {resultType} typed =>
    hasGradeOver_reducesStarPreservation (ctx := typeContext) (term := term) (term' := reduct)
      fxUsageSemiring_isLawful star (grades := grades) (resultType := resultType) typed⟩

/-- **Backed flip (confluence)**: well-graded usage terms are confluent — graded Newman over the
transferred SN. -/
theorem usageAxis_confluence_isBacked :
    fxUsageAxisObligation.capabilities.confluenceStatus = .available
      ∧ (∀ {typeContext : List (GTypeOver fxUsageSemiring)}
          {grades : GradeVectorOver fxUsageSemiring} {term : GradedLambda}
          {resultType : GTypeOver fxUsageSemiring},
          HasGradeOver fxUsageSemiring typeContext grades term resultType →
          ∀ {leftReduct rightReduct : GradedLambda},
            GradedLambda.ReducesStar term leftReduct →
            GradedLambda.ReducesStar term rightReduct →
            Joinable GradedLambda.Reduces leftReduct rightReduct) :=
  ⟨rfl, fun {typeContext} {grades} {term} {resultType} typed {leftReduct} {rightReduct}
      leftStar rightStar =>
    GradedLambda.IsStronglyNormalizing.confluent
      (HasGradeOver.stronglyNormalizing (typeContext := typeContext) (grades := grades)
        (term := term) (resultType := resultType) typed)
      (leftReduct := leftReduct) (rightReduct := rightReduct) leftStar rightStar⟩

/-- **Honest absence (parametricity)**: no usage-indexed relational interpretation is shipped — the
graded `DIM-FUNCTORIAL` projection (a multi-dimension derivation projects to each factor) is a
DIFFERENT statement.  The recorded route: a grade-indexed logical relation over `GradedLambda`. -/
theorem usageAxis_parametricity_isHonestlyAbsent :
    fxUsageAxisObligation.capabilities.parametricityStatus = .unavailable := rfl

/-- **Honest absence (decidable conversion)**: no graded conversion decider is shipped.  The
recorded route is normalize-and-compare over the transferred SN (the ingredients —
`GradedLambda.normalize`, its soundness laws, `DecidableEq GradedLambda` — exist; the decider
does not). -/
theorem usageAxis_decidableConversion_isHonestlyAbsent :
    fxUsageAxisObligation.capabilities.decidableConversionStatus = .unavailable := rfl

/-- **Honest absence (decidable typechecking)**: no decision procedure for `HasGradeOver` is
shipped — the inversion lemmas and the grade-exactness theorem exist; grade inference does not. -/
theorem usageAxis_decidableTypechecking_isHonestlyAbsent :
    fxUsageAxisObligation.capabilities.decidableTypecheckingStatus = .unavailable := rfl

/-- **The graded sconing witness shape** — the BKS witness over the graded λ-calculus: a
computability predicate with the fundamental (well-graded ⟹ computable) and the extraction
(computable ⟹ canonical). -/
structure GradedSconingWitness (isWellGraded : GradedLambda → Prop)
    (isCanonical : GradedLambda → Prop) where
  /-- The displayed computability predicate — the scone over the graded syntax. -/
  computable : GradedLambda → Prop
  /-- FUNDAMENTAL obligation: every well-graded term is computable. -/
  fundamental : ∀ term : GradedLambda, isWellGraded term → computable term
  /-- EXTRACTION obligation: every computable term is canonical. -/
  extraction : ∀ term : GradedLambda, computable term → isCanonical term

/-- A closed term is well-graded at the usage semiring: SOME grade vector and result type type it
in the empty context. -/
def isClosedUsageGraded (term : GradedLambda) : Prop :=
  ∃ (grades : GradeVectorOver fxUsageSemiring) (resultType : GTypeOver fxUsageSemiring),
    HasGradeOver fxUsageSemiring [] grades term resultType

/-- ★ **The usage sconing witness, fundamental DISCHARGED** (the SN-105 headline): the
computability predicate pairs strong normalization with reaches-a-λ-value; the fundamental is a
THEOREM (erasure-transferred SN + `closedReducesToLam` over the lawful usage semiring), not a
hypothesis — the usage dimension's sconing witness is total.  The fundamental respects the grade
arithmetic by construction: it consumes derivations built by the corrected Wood-Atkey rules
(`usageGradeArithmetic_oneAddOne`: `1 + 1 = ω`). -/
def usageSconingWitness :
    GradedSconingWitness isClosedUsageGraded
      (fun term => ∃ body, GradedLambda.ReducesStar term (.lam body)) where
  computable := fun term =>
    GradedLambda.IsStronglyNormalizing term
      ∧ ∃ body, GradedLambda.ReducesStar term (.lam body)
  fundamental := fun _term wellGraded =>
    have ⟨_grades, _resultType, typed⟩ := wellGraded
    ⟨typed.stronglyNormalizing, closedReducesToLam fxUsageSemiring_isLawful typed⟩
  extraction := fun _term computableTerm => computableTerm.2

/-- **The witness yields usage canonicity** by the BKS composition (fundamental then extraction) —
every closed well-graded usage term reaches a λ-value through the scone. -/
theorem usageSconingWitness_canonicity (term : GradedLambda)
    (wellGraded : isClosedUsageGraded term) :
    ∃ body, GradedLambda.ReducesStar term (.lam body) :=
  usageSconingWitness.extraction term (usageSconingWitness.fundamental term wellGraded)

/-- **The SN-108 composition breadcrumb**: meeting the usage ledger against the fully-discharged
type axis preserves it exactly — the SN-103 meet-identity applied at the usage instance. -/
theorem usageAxis_meetWithTypeAxis :
    usageAxisCapabilities.meet fxTypeAxisObligation.capabilities = usageAxisCapabilities :=
  fxTypeAxis_meetPreservesCapabilities usageAxisCapabilities

end FX1Poly.Typed
