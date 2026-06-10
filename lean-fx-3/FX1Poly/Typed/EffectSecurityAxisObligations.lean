import FX1Poly.Typed.UsageAxisObligation
import FX1Poly.Modal.SecurityNoninterferenceGeneral
import FX1Poly.Modal.EffectLatticeClassification
import FX1Poly.Tier0.FireTriangle

/-! # FX1Poly/Typed/EffectSecurityAxisObligations
    — the security + effect AxisObligations: the graded twin and the honest BOTTOM (SN-106, #609)

The third and fourth concrete `AxisObligation`s, completing the capability-lattice SPAN: the type
axis sits at TOP (SN-103), usage and security sit at the same PROPER intermediate point (SN-105 +
this file — the orthogonal-composition thesis at the ledger level), and the effect axis sits at
BOTTOM with its algebra mechanized but no effect-typing judgment shipped.

## The security axis (the graded twin)

  * `securityAxisCapabilities` — the SAME 5-available/3-unavailable ledger as usage, and that
    identity is a THEOREM (`securityAxisCapabilities_eq_usageAxisCapabilities`, `rfl`): both
    dimensions ride the ONE generic `HasGradeOver` engine, so their capability profiles coincide —
    the DIM5 orthogonal-composition thesis read off the ledgers.
  * Five backed flips at `fxSecuritySemiring` (`unclassified < classified`): SN (erasure transfer),
    canonicity (`closedReducesToLam`), normalization (the graded normalizer), subject reduction
    (grades included), confluence (graded Newman) — the same generic theorems, instantiated.
  * `fxSecurityAxisObligation` — Fire-Triangle restriction `some .dependentElimination`: the honest
    semantic assignment — branching on a CLASSIFIED scrutinee is the implicit-flow channel (§12.2),
    so the security dimension restricts dependent elimination into unclassified motives.
  * `securityAxis_parametricityIsAbsent_withFlowHalf` — the honesty form with PARTIAL content: the
    relational noninterference witness ("changing secret inputs does not change unclassified
    outputs") is NOT shipped — the field stays `.unavailable` — but the grade-FLOW half is:
    classified functions and classified arguments POISON application grades
    (`securityClassifiedFunctionPoisonsApplication` / `…ArgumentPoisons…`), conjoined with the
    unavailable pin so the ledger records exactly what exists.
  * `securitySconingWitness` — the discharged witness at the security instance (same shape as
    usage: fundamental and extraction both theorems);
    `securityGradeArithmetic_noImplicitDowngrade` pins `unclassified + classified = classified`
    (mixing public and secret yields secret — no implicit downgrade, §6.1 Dim 5).

## The effect axis (the honest bottom)

  * `effectAxisCapabilities = MetatheoreticCapabilities.bot` — NO capability field is available,
    and the REASON is a theorem, not an apology: `effectAxis_cannotRideGradedEngine` re-exports
    `effectIsNotLawfulOrderedGradeSemiring` — sequential effect composition is the JOIN, which has
    no annihilator, so the effect dimension provably cannot instantiate the semiring `HasGradeOver`
    engine; it needs a lattice-graded judgment that is not yet shipped.
  * What IS mechanized: the effect bounded join-semilattice algebra
    (`effectAxis_algebraIsLawfulLattice` ← `effectIsLawfulBoundedJoinSemilattice`) and the
    Fire-Triangle eval-axis restriction (`some .effects`, admissible by
    `FireTriangleConfig.fromRestriction_admissible` — the SN-104 ∂CBPV content).
  * `effectAxis_meetForcesBot` — the extension-calculus consequence, stated honestly: composing ANY
    profile with the undischarged effect axis zeroes the joint capability ledger (meet with bottom)
    until an effect-typing judgment ships.  SN-108 consumes this as the negative example beside the
    type axis's meet-identity.

## Zero-axiom verification

Capabilities literals, two obligation records, backed-flip conjunctions by direct application of
the shipped generic graded results at `fxSecuritySemiring`, honest-absence pins, re-export
one-liners, and the discharged witness.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Tier0 FX1Poly.Modal

/-! ## The security axis -/

/-- **The security-axis capability ledger** — the same honest 5/3 partial profile as usage: both
dimensions ride the one generic graded engine. -/
def securityAxisCapabilities : MetatheoreticCapabilities where
  canonicityStatus := .available
  normalizationStatus := .available
  parametricityStatus := .unavailable
  subjectReductionStatus := .available
  confluenceStatus := .available
  strongNormalizationStatus := .available
  decidableConversionStatus := .unavailable
  decidableTypecheckingStatus := .unavailable

/-- **The orthogonal-composition thesis at the LEDGER level** (`rfl`): security and usage have
IDENTICAL capability profiles, because both instantiate the same generic `HasGradeOver` metatheory
— no per-dimension proof, no per-dimension capability gap. -/
theorem securityAxisCapabilities_eq_usageAxisCapabilities :
    securityAxisCapabilities = usageAxisCapabilities := rfl

/-- **The security (information-flow) axis obligation**: the §12 dimension over the graded
λ-calculus at `fxSecuritySemiring`, Fire-Triangle restriction `some .dependentElimination` —
branching on a classified scrutinee is the implicit-flow channel (§12.2). -/
def fxSecurityAxisObligation : AxisObligation where
  axisName := "FX security (information-flow) dimension over the graded lambda calculus"
  axisId := .multiModal
  fireTriangleRestriction := some .dependentElimination
  capabilities := securityAxisCapabilities
  estimatedLinesOfCode := 0
  precedents :=
    [⟨"J. A. Goguen, J. Meseguer", "Security policies and security models", none, 1982⟩,
     ⟨"D. Volpano, C. Irvine, G. Smith", "A sound type system for secure flow analysis", none, 1996⟩,
     ⟨"M. Abadi, A. Banerjee, N. Heintze, J. Riecke", "A core calculus of dependency", none, 1999⟩,
     ⟨"A. Sabelfeld, A. C. Myers", "Language-based information-flow security", none, 2003⟩]

/-- **No implicit downgrade, pinned** (`rfl`): mixing public and secret yields secret —
`unclassified + classified = classified` (§6.1 Dim 5 join). -/
theorem securityGradeArithmetic_noImplicitDowngrade :
    fxSecuritySemiring.add SecurityGrade.unclassified SecurityGrade.classified
      = SecurityGrade.classified := rfl

/-- **Backed flip (strong normalization, security)**: the same erasure transfer, instantiated. -/
theorem securityAxis_strongNormalization_isBacked :
    fxSecurityAxisObligation.capabilities.strongNormalizationStatus = .available
      ∧ (∀ {typeContext : List (GTypeOver fxSecuritySemiring)}
          {grades : GradeVectorOver fxSecuritySemiring} {term : GradedLambda}
          {resultType : GTypeOver fxSecuritySemiring},
          HasGradeOver fxSecuritySemiring typeContext grades term resultType →
          GradedLambda.IsStronglyNormalizing term) :=
  ⟨rfl, fun typed => typed.stronglyNormalizing⟩

/-- **Backed flip (canonicity, security)**: closed well-graded security terms reduce to λ-values. -/
theorem securityAxis_canonicity_isBacked :
    fxSecurityAxisObligation.capabilities.canonicityStatus = .available
      ∧ (∀ {grades : GradeVectorOver fxSecuritySemiring} {term : GradedLambda}
          {resultType : GTypeOver fxSecuritySemiring},
          HasGradeOver fxSecuritySemiring [] grades term resultType →
          ∃ body, GradedLambda.ReducesStar term (.lam body)) :=
  ⟨rfl, fun typed => closedReducesToLam fxSecuritySemiring_isLawful typed⟩

/-- **Backed flip (normalization, security)**: every well-graded security term reaches a normal
form via the graded normalizer. -/
theorem securityAxis_normalization_isBacked :
    fxSecurityAxisObligation.capabilities.normalizationStatus = .available
      ∧ (∀ {typeContext : List (GTypeOver fxSecuritySemiring)}
          {grades : GradeVectorOver fxSecuritySemiring} {term : GradedLambda}
          {resultType : GTypeOver fxSecuritySemiring},
          HasGradeOver fxSecuritySemiring typeContext grades term resultType →
          ∃ normalForm : GradedLambda,
            GradedLambda.ReducesStar term normalForm
              ∧ GradedLambda.IsNormalForm normalForm) :=
  ⟨rfl, fun typed =>
    have isTermNormalizing := typed.stronglyNormalizing
    ⟨GradedLambda.normalize _ isTermNormalizing,
     GradedLambda.normalize_reducesStar _ isTermNormalizing,
     GradedLambda.normalize_isNormalForm _ isTermNormalizing⟩⟩

/-- **Backed flip (subject reduction, security)**: security grades are preserved along reduction —
classification cannot be shed by computing. -/
theorem securityAxis_subjectReduction_isBacked :
    fxSecurityAxisObligation.capabilities.subjectReductionStatus = .available
      ∧ (∀ {typeContext : List (GTypeOver fxSecuritySemiring)} {term reduct : GradedLambda},
          GradedLambda.ReducesStar term reduct →
          ∀ {grades : GradeVectorOver fxSecuritySemiring}
            {resultType : GTypeOver fxSecuritySemiring},
            HasGradeOver fxSecuritySemiring typeContext grades term resultType →
            HasGradeOver fxSecuritySemiring typeContext grades reduct resultType) :=
  ⟨rfl, fun {typeContext} {term} {reduct} star {grades} {resultType} typed =>
    hasGradeOver_reducesStarPreservation (ctx := typeContext) (term := term) (term' := reduct)
      fxSecuritySemiring_isLawful star (grades := grades) (resultType := resultType) typed⟩

/-- **Backed flip (confluence, security)**: graded Newman at the security instance. -/
theorem securityAxis_confluence_isBacked :
    fxSecurityAxisObligation.capabilities.confluenceStatus = .available
      ∧ (∀ {typeContext : List (GTypeOver fxSecuritySemiring)}
          {grades : GradeVectorOver fxSecuritySemiring} {term : GradedLambda}
          {resultType : GTypeOver fxSecuritySemiring},
          HasGradeOver fxSecuritySemiring typeContext grades term resultType →
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

/-- **Honest absence WITH the partial content (parametricity, security)**: the RELATIONAL
noninterference witness (changing secret inputs does not change unclassified outputs) is NOT
shipped — the field stays `.unavailable` — but the grade-FLOW half IS: a classified function
poisons every application grade it touches (`securityClassifiedFunctionPoisonsApplication`,
conjoined here so the ledger records exactly what exists).  The binary relational witness is the
recorded route. -/
theorem securityAxis_parametricityIsAbsent_withFlowHalf :
    fxSecurityAxisObligation.capabilities.parametricityStatus = .unavailable
      ∧ (∀ {context : List (GTypeOver fxSecuritySemiring)}
          {grades : GradeVectorOver fxSecuritySemiring}
          {function argument : GradedLambda} {resultType : GTypeOver fxSecuritySemiring},
          HasGradeOver fxSecuritySemiring context grades (.app function argument) resultType →
          ∀ position : Nat,
          ∃ (binderGrade : SecurityGrade) (domain : GTypeOver fxSecuritySemiring)
            (functionGrades argumentGrades : GradeVectorOver fxSecuritySemiring),
            HasGradeOver fxSecuritySemiring context functionGrades function
                (.arrow binderGrade domain resultType) ∧
              HasGradeOver fxSecuritySemiring context argumentGrades argument domain ∧
                (functionGrades.get position = SecurityGrade.classified →
                  grades.get position = SecurityGrade.classified)) :=
  ⟨rfl, fun typed position => securityClassifiedFunctionPoisonsApplication typed position⟩

/-- **Honest absence (decidable conversion, security)** — same gap and route as usage. -/
theorem securityAxis_decidableConversion_isHonestlyAbsent :
    fxSecurityAxisObligation.capabilities.decidableConversionStatus = .unavailable := rfl

/-- **Honest absence (decidable typechecking, security)** — same gap and route as usage. -/
theorem securityAxis_decidableTypechecking_isHonestlyAbsent :
    fxSecurityAxisObligation.capabilities.decidableTypecheckingStatus = .unavailable := rfl

/-- A closed term is well-graded at the security semiring. -/
def isClosedSecurityGraded (term : GradedLambda) : Prop :=
  ∃ (grades : GradeVectorOver fxSecuritySemiring) (resultType : GTypeOver fxSecuritySemiring),
    HasGradeOver fxSecuritySemiring [] grades term resultType

/-- **The security sconing witness, fundamental DISCHARGED** — the same total shape as the usage
witness, at the security instance: both obligations are theorems. -/
def securitySconingWitness :
    GradedSconingWitness isClosedSecurityGraded
      (fun term => ∃ body, GradedLambda.ReducesStar term (.lam body)) where
  computable := fun term =>
    GradedLambda.IsStronglyNormalizing term
      ∧ ∃ body, GradedLambda.ReducesStar term (.lam body)
  fundamental := fun _term wellGraded =>
    have ⟨_grades, _resultType, typed⟩ := wellGraded
    ⟨typed.stronglyNormalizing, closedReducesToLam fxSecuritySemiring_isLawful typed⟩
  extraction := fun _term computableTerm => computableTerm.2

/-! ## The effect axis -/

/-- **The effect-axis capability ledger** — the honest BOTTOM: no metatheoretic capability is
available, because no effect-typing judgment is shipped (and the graded engine provably cannot
carry one — see `effectAxis_cannotRideGradedEngine`). -/
def effectAxisCapabilities : MetatheoreticCapabilities :=
  MetatheoreticCapabilities.bot

/-- The effect ledger is the bottom of the capability lattice, pinned. -/
theorem effectAxisCapabilities_eq_bot :
    effectAxisCapabilities = MetatheoreticCapabilities.bot := rfl

/-- **The effect axis obligation**: the §9 effect dimension — algebra mechanized (the bounded
join-semilattice), judgment not yet shipped, Fire-Triangle eval-axis restriction `some .effects`
(the SN-104 ∂CBPV content). -/
def fxEffectAxisObligation : AxisObligation where
  axisName := "FX effect dimension (bounded join-semilattice algebra; typing judgment pending)"
  axisId := .multiModal
  fireTriangleRestriction := some .effects
  capabilities := effectAxisCapabilities
  estimatedLinesOfCode := 0
  precedents :=
    [⟨"E. Moggi", "Notions of computation and monads", none, 1991⟩,
     ⟨"G. Plotkin, J. Power", "Notions of computation determine monads", none, 2002⟩,
     ⟨"P. B. Levy", "Call-by-push-value: A functional/imperative synthesis", none, 2004⟩,
     ⟨"P.-M. Pedrot, N. Tabareau", "The fire triangle: how to mix substitution, dependent elimination, and effects", none, 2020⟩]

/-- **The REASON the effect ledger is bottom, as a theorem**: the effect dimension provably cannot
ride the semiring `HasGradeOver` engine — sequential effect composition is the JOIN, which has no
annihilator (`effectIsNotLawfulOrderedGradeSemiring`).  A lattice-graded typing judgment is the
recorded route. -/
theorem effectAxis_cannotRideGradedEngine :
    ¬ IsLawfulOrderedGradeSemiring effectSemiringCandidate :=
  effectIsNotLawfulOrderedGradeSemiring

/-- **What IS mechanized for the effect axis**: its algebra — the effect bounded join-semilattice
is lawful (`effectIsLawfulBoundedJoinSemilattice`, the DIM-CLASS classification). -/
theorem effectAxis_algebraIsLawfulLattice :
    IsLawfulBoundedJoinSemilattice effectLattice :=
  effectIsLawfulBoundedJoinSemilattice

/-- **The effect Fire-Triangle restriction is admissible**: restricting the effects leg leaves an
admissible two-leg configuration (the SN-104 ∂CBPV navigation). -/
theorem effectAxis_fireTriangleAdmissible :
    (FireTriangleConfig.fromRestriction
      fxEffectAxisObligation.fireTriangleRestriction).isAdmissible = true :=
  FireTriangleConfig.fromRestriction_admissible (some .effects)

/-- **The extension-calculus consequence of the bottom ledger, stated honestly**: composing ANY
capability profile with the undischarged effect axis zeroes the joint ledger — the negative
example SN-108 consumes beside the type axis's meet-identity.  An effect-typing judgment is what
lifts this. -/
theorem effectAxis_meetForcesBot (cap : MetatheoreticCapabilities) :
    cap.meet fxEffectAxisObligation.capabilities = MetatheoreticCapabilities.bot :=
  MetatheoreticCapabilities.meet_bot_right cap

end FX1Poly.Typed
