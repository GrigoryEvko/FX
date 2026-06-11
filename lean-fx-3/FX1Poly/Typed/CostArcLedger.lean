import FX1Poly.Typed.CostAwareEquivalence
import FX1Poly.Typed.OptimizationCell
import FX1Poly.Typed.ChurchNumeralAsymptotics
import FX1Poly.Typed.WellTypedSpaceCalculable
import FX1Poly.Modal.GradedCostFundamental
import FX1Poly.Modal.GradedLinearTimeBound
import FX1Poly.Typed.RawStepNotStronglyNormalizing

/-! # FX1Poly/Typed/CostArcLedger
    — ★ the COST-arc capstone: the honest frontier ledger, proven / impossible / open (COST-9)

The §6.3 Dim-13/15 cost story, signed off the HCAP way: every cell is a
named status pin, every PROVEN pin is backed by a theorem restating (a
representative of) the shipped result, every IMPOSSIBLE pin is backed
by the shipped REFUTATION, and the OPEN cells are recorded without
invented content.  The counts are kernel-computed pins.

PROVEN (9): exact canonical cost (COST-1/3) · worst-case bound for
every strategy (COST-1/3) · the grade→cost tie (COST-2, the cost-indexed
logical relation) · the strict-linear LINEAR-TIME class (COST-2a) ·
typed cost totality (COST-3, every well-typed program) · typed space
totality (COST-3) · the improvement preorder with normalizer-optimality
(COST-4) · Church arithmetic in verified bounded time with EXACT closed
forms (COST-8) · verified optimization cells (OPT-0).

IMPOSSIBLE (3, each a mechanized refutation): cost is NOT Conv-invariant
(the COST-4 no-go — cost-aware equivalence is strictly finer than
definitional equality) · affine zero-scaling does NOT bound occurrence
counts (the COST-2a refutation — the linear-time class needs the STRICT
hypothesis) · raw cost totality (Ω diverges — the calculators' typing
hypothesis is essential).

OPEN (4, recorded honestly): the calf phase distinction through the STC
modalities (COST-5) · the PolyBound index language (COST-7) ·
dimension-2 cost (transport/proof cost of equivalence cells) · the
quantified time-space tradeoff.  Also open IN PRINCIPLE and never
claimed: tight automatic inference for arbitrary programs (Rice).

Zero-axiom; gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core
open FX1Poly.Modal
open FX1Poly.Universe

/-- Frontier status of one cost-arc claim. -/
inductive CostClaimStatus where
  /-- Shipped, zero-axiom, gated. -/
  | proven : CostClaimStatus
  /-- Mechanically REFUTED — provably not achievable as stated. -/
  | impossible : CostClaimStatus
  /-- Genuinely open; recorded without invented content. -/
  | openProblem : CostClaimStatus
deriving DecidableEq

/-- Bool classifier for the count pins. -/
def CostClaimStatus.isProvenB : CostClaimStatus → Bool
  | .proven => true
  | .impossible => false
  | .openProblem => false

/-- Bool classifier for the count pins. -/
def CostClaimStatus.isImpossibleB : CostClaimStatus → Bool
  | .proven => false
  | .impossible => true
  | .openProblem => false

/-- One cost-arc frontier cell. -/
structure CostArcCell where
  claimName : String
  status : CostClaimStatus

/-- ★ The cost-arc frontier ledger — 9 proven, 3 impossible, 4 open. -/
def costArcLedger : List CostArcCell :=
  [⟨"exact canonical evaluation cost (graded + kernel)", .proven⟩,
   ⟨"worst-case cost bound, every strategy", .proven⟩,
   ⟨"grade -> cost tie (cost-indexed logical relation)", .proven⟩,
   ⟨"strict-linear terms evaluate in linear time", .proven⟩,
   ⟨"every well-typed program has calculable cost", .proven⟩,
   ⟨"every well-typed program has calculable space", .proven⟩,
   ⟨"decidable improvement preorder; normalizer is optimal", .proven⟩,
   ⟨"Church arithmetic in verified bounded time (exact closed forms)", .proven⟩,
   ⟨"verified optimization cells with composable certificates", .proven⟩,
   ⟨"cost as a Conv-class property", .impossible⟩,
   ⟨"affine zero-scaling bounds occurrence counts", .impossible⟩,
   ⟨"total cost calculators on RAW terms", .impossible⟩,
   ⟨"calf phase distinction through the STC modalities", .openProblem⟩,
   ⟨"PolyBound index language (the cost O(n) declarations)", .openProblem⟩,
   ⟨"dimension-2 cost (transport cost of equivalence cells)", .openProblem⟩,
   ⟨"quantified time-space tradeoff", .openProblem⟩]

/-- The ledger counts, kernel-computed: 16 cells — 9 proven, 3
impossible, 4 open. -/
theorem costArcLedger_counts :
    costArcLedger.length = 16
      ∧ (costArcLedger.filter (fun cell => cell.status.isProvenB)).length = 9
      ∧ (costArcLedger.filter (fun cell => cell.status.isImpossibleB)).length = 3 :=
  ⟨rfl, rfl, rfl⟩

/-! ## Backing the PROVEN column (representatives of the shipped results) -/

/-- Backed: the exact canonical cost — a genuine counted chain of exactly
`normalizeCost` steps to THE normal form (COST-3 brick 1). -/
theorem costLedger_exactCost_isBacked :
    ∀ {scope : Nat} (term : RawTerm scope)
      (accessible : Acc (@StepStar.StepSuccessor scope) term),
      StepStarN (RawTerm.normalizeCost term accessible) term
        (RawTerm.normalize term accessible) :=
  RawTerm.normalizeCost_isExact

/-- Backed: the worst-case bound — no counted chain under ANY strategy
exceeds `costBound` (COST-3 brick 4). -/
theorem costLedger_worstCase_isBacked :
    ∀ {scope : Nat} {term : RawTerm scope}
      (accessible : Acc (@StepStar.StepSuccessor scope) term)
      {steps : Nat} {target : RawTerm scope},
      StepStarN steps term target → steps ≤ RawTerm.costBound term accessible :=
  fun {_scope} {_term} accessible {_steps} {_target} chain =>
    RawTerm.costBound_isSound accessible chain

/-- Backed: the grade→cost tie — every well-graded term at the complexity
semiring is cost-reducible at its grade-weighted budget (COST-2, the
cost-indexed logical relation fundamental theorem). -/
theorem costLedger_gradeCostTie_isBacked :
    ∀ {typeContext : List (GTypeOver fxComplexitySemiring)}
      {grades : GradeVectorOver fxComplexitySemiring} {term : GradedLambda}
      {resultType : GTypeOver fxComplexitySemiring},
      HasGradeOver fxComplexitySemiring typeContext grades term resultType →
      ∃ (intrinsicWeight : Nat),
        ∀ (substitution : TermSubstitution) (budgetAssignment : Nat → Nat),
          CostReducibleSubstitution typeContext budgetAssignment substitution →
          CostReducible resultType
            (weightedBudget grades budgetAssignment + intrinsicWeight)
            (GradedLambda.applySubstitution substitution term) :=
  fun {_typeContext} {_grades} {_term} {_resultType} typed => typed.costFundamental

/-- Backed: the LINEAR-TIME class — strict-linear well-graded terms
evaluate in fewer steps than their size, under ANY strategy (COST-2a). -/
theorem costLedger_linearTime_isBacked :
    ∀ {ctx : List (GTypeOver fxUsageSemiring)}
      {grades : GradeVectorOver fxUsageSemiring} {term : GradedLambda}
      {resultType : GTypeOver fxUsageSemiring},
      HasStrictLinearGrade ctx grades term resultType →
      ∀ {steps : Nat} {target : GradedLambda},
        GradedLambda.ReducesInSteps term steps target → steps < term.size :=
  fun {_ctx} {_grades} {_term} {_resultType} typed {_steps} {_target} chain =>
    typed.linearTime chain

/-- Backed: typed cost totality — the calculator is sound on every closed
well-typed program (COST-3 brick 5, the soundness projection). -/
theorem costLedger_typedCost_isBacked :
    ∀ {profile : PolyProfile} {subject classifier : RawTerm 0}
      (derivation : HasTypeDescPi profile
        (TypingContext.empty : TypingContext profile 0) subject classifier)
      {steps : Nat} {target : RawTerm 0},
      StepStarN steps subject target → steps ≤ derivation.costCalculator :=
  fun {_profile} {_subject} {_classifier} derivation {_steps} {_target} chain =>
    derivation.costCalculator_isSound chain

/-- Backed: typed space totality — every canonically-visited term of a
closed well-typed program is size-bounded (COST-3 brick 6). -/
theorem costLedger_typedSpace_isBacked :
    ∀ {profile : PolyProfile} {subject classifier : RawTerm 0}
      (derivation : HasTypeDescPi profile
        (TypingContext.empty : TypingContext profile 0) subject classifier)
      {intermediate : RawTerm 0},
      RawTerm.OnCanonicalPath subject intermediate →
      RawTerm.size intermediate ≤ derivation.spaceCalculator :=
  fun {_profile} {_subject} {_classifier} derivation {_intermediate} visited =>
    derivation.spaceCalculator_isSound visited

/-- Backed: the improvement preorder's optimality — the normal form
improves on EVERY convertible closed well-typed program (COST-4). -/
theorem costLedger_improvementOptimality_isBacked :
    ∀ {profile : PolyProfile} {subject classifier otherSubject otherClassifier : RawTerm 0}
      (derivation : HasTypeDescPi profile
        (TypingContext.empty : TypingContext profile 0) subject classifier)
      (otherDerivation : HasTypeDescPi profile
        (TypingContext.empty : TypingContext profile 0) otherSubject otherClassifier),
      Conv subject otherSubject →
      derivation.normalFormDerivation.Improves otherDerivation :=
  fun {_profile} {_s} {_c} {_os} {_oc} derivation otherDerivation convertible =>
    derivation.normalFormDerivation_improvesAllConvertible otherDerivation convertible

/-- Backed: Church arithmetic in verified bounded time — the
multiplication representative (the sharpest count: exactly `3·m + 3`,
independent of the right operand; COST-8). -/
theorem costLedger_churchBoundedTime_isBacked :
    ∀ (countLeft countRight : Nat) (typeA handlerF baseX : RawTerm 0),
      StepStarN (3 * countLeft + 3)
        (appCell (appCell (appCell (churchNumeralLambda countLeft) typeA)
          (appCell (appCell (churchNumeralLambda countRight) typeA) handlerF)) baseX)
        (iteratedApplication (countLeft * countRight) handlerF baseX) :=
  churchMultiplication_dispatchCounted

/-- Backed: verified optimization cells — the demonstrator cell is
STRICTLY cost-decreasing (OPT-0). -/
theorem costLedger_optimizationCells_isBacked :
    ∀ {profile : PolyProfile}, (betaRewriteCell profile).IsStrict :=
  betaRewriteCell_isStrict

/-! ## Backing the IMPOSSIBLE column (the mechanized refutations) -/

/-- Refuted: cost as a Conv-class property — two convertible closed terms
with provably different canonical costs (the COST-4 no-go). -/
theorem costLedger_convInvariance_isRefuted :
    ∃ (left right : RawTerm 0)
      (leftAccessible : Acc (@StepStar.StepSuccessor 0) left)
      (rightAccessible : Acc (@StepStar.StepSuccessor 0) right),
      Conv left right
        ∧ RawTerm.normalizeCost left leftAccessible
            ≠ RawTerm.normalizeCost right rightAccessible :=
  costIsNotConvInvariant

/-- Refuted: affine zero-scaling bounding occurrence counts — the
committed leak witness (the COST-2a refutation; the linear-time class
genuinely needs the STRICT hypothesis). -/
theorem costLedger_affineScaling_isRefuted :
    ¬ UsageGrade.boundsCount UsageGrade.zero
        (GradedLambda.countOccurrencesAt 0 affineDuplicatorBody) :=
  affineGradeZero_doesNotBoundCount

/-- Refuted: total cost calculators on RAW terms — Ω is not strongly
normalizing, so the accessibility the calculators recurse over does not
exist; the typing hypothesis is essential. -/
theorem costLedger_rawTotality_isRefuted :
    ¬ StepStar.IsStronglyNormalizing divergentOmegaCell :=
  divergentOmega_notStronglyNormalizing

end FX1Poly.Typed
