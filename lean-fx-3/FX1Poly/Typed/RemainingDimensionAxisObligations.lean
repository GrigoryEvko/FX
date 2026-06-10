import FX1Poly.Typed.EffectSecurityAxisObligations
import FX1Poly.Modal.ComplexitySemiring
import FX1Poly.Modal.ClockDomainLatticeDimension
import FX1Poly.Modal.ProvenanceLatticeDimension
import FX1Poly.Modal.PreorderDimension

/-! # FX1Poly/Typed/RemainingDimensionAxisObligations
    — the remaining-dimensions AxisObligation batch: one generic graded bundle + the algebra-tier and
    pending-tier records (SN-107, #610)

The batch discharge completing the per-dimension obligation gallery.  Three honesty tiers:

  * **The graded tier (complexity — the THIRD graded sibling).**
    ★ `gradedAxis_fiveCapabilitiesBacked` — the GENERIC five-capability bundle over ANY lawful
    ordered grade semiring: strong normalization, closed canonicity, normalization, subject
    reduction, and confluence, in one conjunction.  This is the common generalization the usage and
    security modules instantiated piecewise — stated once, it discharges every present and future
    semiring dimension in one application.  `fxComplexityAxisObligation` instantiates it at the
    cost/space N-semiring (`fxComplexitySemiring`, DIM3-1), with the ledger identity
    `complexityAxisCapabilities_eq_usageAxisCapabilities` (`rfl`) extending the
    orthogonal-composition thesis to a THREE-dimension family: usage, security, and complexity
    carry literally the same capability profile because they ride the same engine.
  * **The algebra tier (trust, clock, provenance, lifetime).**  Each at capability BOTTOM with its
    mechanized algebra cited by re-export: trust is a lawful bounded join-semilattice AND provably
    not a grade semiring (the effect-shaped pair); clock and provenance are lawful lattices
    (parameterized / infinite); lifetime is a genuine PREORDER and provably NOT antisymmetric
    (`lifetimeIsNotAntisymmetric`) — it cannot even be presented as a join-semilattice, the honest
    structural reason its entry differs from the lattice family.
  * **The pending tier (refinement, representation, observability).**  Obligations recorded at
    BOTTOM with NO algebra citation — none is mechanized — and a non-zero `estimatedLinesOfCode`
    (the field's first honest non-trivial use): refinement needs an SMT-obligation model, repr a
    layout-constraint preorder, observability a two-point flow lattice (the security recipe).
    Recording the obligation without inventing content IS the honest move; the records make the
    gaps auditable.

`remainingDimensionObligations` lists the batch (8 records) with a count pin.  Composition with the
discharged type axis follows the SN-103/SN-106 pattern: the graded complexity entry meets
losslessly; every bottom entry forces bottom (`MetatheoreticCapabilities.meet_bot_right`) until its
judgment ships — the two ends SN-108 consumes.

## Zero-axiom verification

One generic conjunction proved from the shipped generic graded results, obligation literals,
`rfl` ledger pins, and algebra re-exports.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTypedSubstVecCwR.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Tier0 FX1Poly.Modal

/-! ## The generic graded bundle -/

/-- ★ **The generic five-capability bundle**: over ANY lawful ordered grade semiring, the graded
λ-calculus has strong normalization (the erasure transfer), closed canonicity (reaches a λ-value),
normalization (the graded normalizer), subject reduction (grades included), and confluence (graded
Newman) — in ONE conjunction.  The common generalization of the usage and security per-axis flips;
every present and future semiring dimension discharges by one application. -/
theorem gradedAxis_fiveCapabilitiesBacked (R : OrderedGradeSemiring)
    (lawful : IsLawfulOrderedGradeSemiring R) :
    (∀ {typeContext : List (GTypeOver R)} {grades : GradeVectorOver R}
        {term : GradedLambda} {resultType : GTypeOver R},
        HasGradeOver R typeContext grades term resultType →
        GradedLambda.IsStronglyNormalizing term)
      ∧ (∀ {grades : GradeVectorOver R} {term : GradedLambda} {resultType : GTypeOver R},
          HasGradeOver R [] grades term resultType →
          ∃ body, GradedLambda.ReducesStar term (.lam body))
      ∧ (∀ {typeContext : List (GTypeOver R)} {grades : GradeVectorOver R}
          {term : GradedLambda} {resultType : GTypeOver R},
          HasGradeOver R typeContext grades term resultType →
          ∃ normalForm : GradedLambda,
            GradedLambda.ReducesStar term normalForm
              ∧ GradedLambda.IsNormalForm normalForm)
      ∧ (∀ {typeContext : List (GTypeOver R)} {term reduct : GradedLambda},
          GradedLambda.ReducesStar term reduct →
          ∀ {grades : GradeVectorOver R} {resultType : GTypeOver R},
            HasGradeOver R typeContext grades term resultType →
            HasGradeOver R typeContext grades reduct resultType)
      ∧ (∀ {typeContext : List (GTypeOver R)} {grades : GradeVectorOver R}
          {term : GradedLambda} {resultType : GTypeOver R},
          HasGradeOver R typeContext grades term resultType →
          ∀ {leftReduct rightReduct : GradedLambda},
            GradedLambda.ReducesStar term leftReduct →
            GradedLambda.ReducesStar term rightReduct →
            Joinable GradedLambda.Reduces leftReduct rightReduct) :=
  ⟨fun typed => typed.stronglyNormalizing,
   fun typed => closedReducesToLam lawful typed,
   fun typed =>
     have isTermNormalizing := typed.stronglyNormalizing
     ⟨GradedLambda.normalize _ isTermNormalizing,
      GradedLambda.normalize_reducesStar _ isTermNormalizing,
      GradedLambda.normalize_isNormalForm _ isTermNormalizing⟩,
   fun {typeContext} {term} {reduct} star {grades} {resultType} typed =>
     hasGradeOver_reducesStarPreservation (ctx := typeContext) (term := term) (term' := reduct)
       lawful star (grades := grades) (resultType := resultType) typed,
   fun {typeContext} {grades} {term} {resultType} typed {leftReduct} {rightReduct}
       leftStar rightStar =>
     GradedLambda.IsStronglyNormalizing.confluent
       (HasGradeOver.stronglyNormalizing (typeContext := typeContext) (grades := grades)
         (term := term) (resultType := resultType) typed)
       (leftReduct := leftReduct) (rightReduct := rightReduct) leftStar rightStar⟩

/-! ## The complexity axis (the third graded sibling) -/

/-- The complexity-axis ledger — the same 5/3 profile as usage and security. -/
def complexityAxisCapabilities : MetatheoreticCapabilities where
  canonicityStatus := .available
  normalizationStatus := .available
  parametricityStatus := .unavailable
  subjectReductionStatus := .available
  confluenceStatus := .available
  strongNormalizationStatus := .available
  decidableConversionStatus := .unavailable
  decidableTypecheckingStatus := .unavailable

/-- **The orthogonal-composition thesis now spans a THREE-dimension family** (`rfl`): usage,
security, and complexity carry literally the same capability profile — one generic engine, three
instances, zero per-dimension metatheory. -/
theorem complexityAxisCapabilities_eq_usageAxisCapabilities :
    complexityAxisCapabilities = usageAxisCapabilities := rfl

/-- **The complexity (cost/space) axis obligation**: the §6.3 Dim 13/15 N-semiring dimension over
the graded λ-calculus — costs add in parallel and sequentially, zero is free. -/
def fxComplexityAxisObligation : AxisObligation where
  axisName := "FX complexity (cost/space) dimension over the graded lambda calculus"
  axisId := .multiModal
  fireTriangleRestriction := none
  capabilities := complexityAxisCapabilities
  estimatedLinesOfCode := 0
  precedents :=
    [⟨"D. Ghica, A. Smith", "Bounded linear types in a resource semiring", none, 2014⟩,
     ⟨"A. Brunel, M. Gaboardi, D. Mazza, S. Zdancewic", "A core quantitative coeffect calculus", none, 2014⟩,
     ⟨"R. Atkey", "Syntax and Semantics of Quantitative Type Theory", none, 2018⟩]

/-- **The complexity axis discharges by ONE application of the generic bundle** — the five backed
capabilities at `fxComplexitySemiring`, conjoined with the ledger fields they back. -/
theorem complexityAxis_fiveCapabilitiesBacked :
    (fxComplexityAxisObligation.capabilities.strongNormalizationStatus = .available
        ∧ fxComplexityAxisObligation.capabilities.canonicityStatus = .available
        ∧ fxComplexityAxisObligation.capabilities.normalizationStatus = .available
        ∧ fxComplexityAxisObligation.capabilities.subjectReductionStatus = .available
        ∧ fxComplexityAxisObligation.capabilities.confluenceStatus = .available)
      ∧ ((∀ {typeContext : List (GTypeOver fxComplexitySemiring)}
            {grades : GradeVectorOver fxComplexitySemiring}
            {term : GradedLambda} {resultType : GTypeOver fxComplexitySemiring},
            HasGradeOver fxComplexitySemiring typeContext grades term resultType →
            GradedLambda.IsStronglyNormalizing term)
          ∧ (∀ {grades : GradeVectorOver fxComplexitySemiring} {term : GradedLambda}
              {resultType : GTypeOver fxComplexitySemiring},
              HasGradeOver fxComplexitySemiring [] grades term resultType →
              ∃ body, GradedLambda.ReducesStar term (.lam body))
          ∧ (∀ {typeContext : List (GTypeOver fxComplexitySemiring)}
              {grades : GradeVectorOver fxComplexitySemiring}
              {term : GradedLambda} {resultType : GTypeOver fxComplexitySemiring},
              HasGradeOver fxComplexitySemiring typeContext grades term resultType →
              ∃ normalForm : GradedLambda,
                GradedLambda.ReducesStar term normalForm
                  ∧ GradedLambda.IsNormalForm normalForm)
          ∧ (∀ {typeContext : List (GTypeOver fxComplexitySemiring)} {term reduct : GradedLambda},
              GradedLambda.ReducesStar term reduct →
              ∀ {grades : GradeVectorOver fxComplexitySemiring}
                {resultType : GTypeOver fxComplexitySemiring},
                HasGradeOver fxComplexitySemiring typeContext grades term resultType →
                HasGradeOver fxComplexitySemiring typeContext grades reduct resultType)
          ∧ (∀ {typeContext : List (GTypeOver fxComplexitySemiring)}
              {grades : GradeVectorOver fxComplexitySemiring}
              {term : GradedLambda} {resultType : GTypeOver fxComplexitySemiring},
              HasGradeOver fxComplexitySemiring typeContext grades term resultType →
              ∀ {leftReduct rightReduct : GradedLambda},
                GradedLambda.ReducesStar term leftReduct →
                GradedLambda.ReducesStar term rightReduct →
                Joinable GradedLambda.Reduces leftReduct rightReduct)) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl⟩,
   gradedAxis_fiveCapabilitiesBacked fxComplexitySemiring fxComplexitySemiring_isLawful⟩

/-! ## The algebra tier: trust, clock, provenance, lifetime -/

/-- **The trust axis obligation** — capability bottom, algebra mechanized (the effect-shaped
pair). -/
def fxTrustAxisObligation : AxisObligation where
  axisName := "FX trust dimension (weakest-link bounded join-semilattice; judgment pending)"
  axisId := .multiModal
  fireTriangleRestriction := none
  capabilities := MetatheoreticCapabilities.bot
  estimatedLinesOfCode := 0
  precedents :=
    [⟨"A. Sabelfeld, A. C. Myers", "Language-based information-flow security", none, 2003⟩]

/-- Trust provably cannot ride the semiring engine (weakest-link combine has no annihilator) —
the same shape as effect. -/
theorem trustAxis_cannotRideGradedEngine :
    ¬ IsLawfulOrderedGradeSemiring trustSemiringCandidate :=
  trustIsNotLawfulOrderedGradeSemiring

/-- Trust's mechanized algebra: the lawful weakest-link bounded join-semilattice. -/
theorem trustAxis_algebraIsLawfulLattice :
    IsLawfulBoundedJoinSemilattice trustLattice :=
  trustIsLawfulBoundedJoinSemilattice

/-- **The clock-domain axis obligation** — capability bottom, algebra mechanized (the first
parameterized, infinite-carrier lattice). -/
def fxClockAxisObligation : AxisObligation where
  axisName := "FX clock-domain dimension (parameterized bounded join-semilattice; judgment pending)"
  axisId := .multiModal
  fireTriangleRestriction := none
  capabilities := MetatheoreticCapabilities.bot
  estimatedLinesOfCode := 0
  precedents :=
    [⟨"E. A. Lee, A. Sangiovanni-Vincentelli", "A framework for comparing models of computation", none, 1998⟩]

/-- Clock's mechanized algebra: the lawful clock-domain lattice (combinational bottom,
cross-domain error top). -/
theorem clockAxis_algebraIsLawfulLattice :
    IsLawfulBoundedJoinSemilattice clockLattice :=
  clockIsLawfulBoundedJoinSemilattice

/-- **The provenance axis obligation** — capability bottom, algebra mechanized (the first infinite
FULL lattice). -/
def fxProvenanceAxisObligation : AxisObligation where
  axisName := "FX provenance dimension (infinite full lattice of origin labels; judgment pending)"
  axisId := .multiModal
  fireTriangleRestriction := none
  capabilities := MetatheoreticCapabilities.bot
  estimatedLinesOfCode := 0
  precedents :=
    [⟨"J. Cheney, A. Ahmed, U. A. Acar", "Provenance as dependency analysis", none, 2011⟩]

/-- Provenance's mechanized algebra: the lawful origin-label lattice. -/
theorem provenanceAxis_algebraIsLawfulLattice :
    IsLawfulBoundedJoinSemilattice provenanceLattice :=
  provenanceIsLawfulBoundedJoinSemilattice

/-- **The lifetime axis obligation** — capability bottom, algebra mechanized as a genuine
PREORDER. -/
def fxLifetimeAxisObligation : AxisObligation where
  axisName := "FX lifetime dimension (outlives preorder, non-antisymmetric; judgment pending)"
  axisId := .multiModal
  fireTriangleRestriction := none
  capabilities := MetatheoreticCapabilities.bot
  estimatedLinesOfCode := 0
  precedents :=
    [⟨"M. Tofte, J.-P. Talpin", "Region-based memory management", none, 1997⟩,
     ⟨"N. D. Matsakis, F. S. Klock", "The Rust language", none, 2014⟩]

/-- **Lifetime is provably NOT antisymmetric** — distinct regions can mutually outlive each other —
so it cannot even be presented as a join-semilattice: the honest structural reason its entry
differs from the lattice family (the §6.3 Dim 7 preorder class, the first non-antisymmetric
dimension). -/
theorem lifetimeAxis_algebraIsProperPreorder :
    ¬ lifetimePreorder.IsAntisymmetric :=
  lifetimeIsNotAntisymmetric

/-! ## The pending tier: refinement, representation, observability -/

/-- **The refinement axis obligation, recorded undischarged**: no algebra is mechanized; the route
is an SMT-obligation model (predicates collected during elaboration, discharged at trust
boundaries).  The non-zero estimate is the field's honest use. -/
def fxRefinementAxisObligation : AxisObligation where
  axisName := "FX refinement dimension (SMT-obligation model; NOT YET MECHANIZED)"
  axisId := .multiModal
  fireTriangleRestriction := none
  capabilities := MetatheoreticCapabilities.bot
  estimatedLinesOfCode := 4000
  precedents :=
    [⟨"P. M. Rondon, M. Kawaguchi, R. Jhala", "Liquid types", none, 2008⟩,
     ⟨"N. Swamy et al.", "Dependent types and multi-monadic effects in F*", none, 2016⟩]

/-- **The representation axis obligation, recorded undischarged**: the route is a layout-constraint
preorder (`repr(Native) <= repr(C)`). -/
def fxRepresentationAxisObligation : AxisObligation where
  axisName := "FX representation dimension (layout-constraint preorder; NOT YET MECHANIZED)"
  axisId := .multiModal
  fireTriangleRestriction := none
  capabilities := MetatheoreticCapabilities.bot
  estimatedLinesOfCode := 1500
  precedents :=
    [⟨"G. Necula, S. McPeak, W. Weimer", "CCured: type-safe retrofitting of legacy code", none, 2002⟩]

/-- **The observability axis obligation, recorded undischarged**: the route is the two-point
`opaque < transparent` flow lattice — the security recipe at a different pair of labels. -/
def fxObservabilityAxisObligation : AxisObligation where
  axisName := "FX observability dimension (opaque/transparent two-point lattice; NOT YET MECHANIZED)"
  axisId := .multiModal
  fireTriangleRestriction := none
  capabilities := MetatheoreticCapabilities.bot
  estimatedLinesOfCode := 1000
  precedents :=
    [⟨"D. Molnar, M. Piotrowski, D. Schultz, D. Wagner", "The program counter security model", none, 2005⟩]

/-! ## The batch -/

/-- The SN-107 batch: the eight remaining-dimension obligations in one list — one graded
discharge, four algebra-tier records, three pending-tier records. -/
def remainingDimensionObligations : List AxisObligation :=
  [fxComplexityAxisObligation, fxTrustAxisObligation, fxClockAxisObligation,
   fxProvenanceAxisObligation, fxLifetimeAxisObligation, fxRefinementAxisObligation,
   fxRepresentationAxisObligation, fxObservabilityAxisObligation]

/-- The batch covers exactly eight dimensions — the count pin. -/
theorem remainingDimensionObligations_count :
    remainingDimensionObligations.length = 8 := rfl

end FX1Poly.Typed
