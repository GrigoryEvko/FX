import FX1Poly.Core.CostConvInvariance
import FX1Poly.Typed.WellTypedCostCalculable
import FX1Poly.Typed.HasTypeDescPiSubjectReductionUnconditional

/-! # FX1Poly/Typed/CostAwareEquivalence
    — ★ cost-aware equivalence + the improvement preorder, DECIDABLE on closed well-typed programs (COST-4)

The constructive answer to the Conv-invariance NO-GO
(`costIsNotConvInvariant`): since cost is destroyed by extensional
quotienting, the cost-aware notions live STRICTLY FINER than `Conv`,
over derivations (which carry the SN witnesses the costs need):

  * `HasTypeDescPi.Improves` — the IMPROVEMENT PREORDER: convertible
    (same extensional behavior) and canonical cost no larger.  The
    relation every verified optimization must land in (the OPT-arc
    substrate: a verified rewrite is exactly an `Improves` witness).
    Reflexive + transitive (`Conv.trans` is unconditional at the
    kernel).
  * `HasTypeDescPi.CostEquiv` — cost-aware EQUIVALENCE: convertible
    AND exactly equal canonical cost.  An equivalence relation; it is
    the symmetrization of `Improves`
    (`CostEquiv.ofImprovesBoth` / `.improves` / `.improvesReverse`),
    and it TRANSPORTS cost (`CostEquiv.costEq` — the property `Conv`
    provably lacks).
  * ★ `HasTypeDescPi.normalFormDerivation_improvesAllConvertible` —
    **the normalizer is improvement-OPTIMAL**: the (re-typed) normal
    form improves on EVERY derivation whose subject is convertible to
    the original — zero canonical cost, same Conv class.  The cost-
    minimum of each Conv class of closed well-typed programs is its
    normal form.
  * ★ `decideImproves` / `decideCostEquiv` — both relations are
    DECIDABLE on closed well-typed programs: `Conv` decides by
    normalize-and-compare (`Conv.decidableOfStronglyNormalizing`, SN
    from typing), and the cost comparison is a `Nat` test.
  * Non-vacuity: a concrete STRICT improvement — the typed β-redex
    `(λx:Type@1. x)(Type@0)` is improved by its reduct, and NOT
    conversely (the redex's nonzero cost against the reduct's zero).

Zero-axiom; gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core
open FX1Poly.Universe
open StepStar

/-! ## The improvement preorder and cost-aware equivalence -/

/-- **The improvement preorder**: same extensional behavior (`Conv`),
canonical cost no larger.  A verified optimization is exactly an
`Improves` witness from the optimized program to the original. -/
def HasTypeDescPi.Improves {profile : PolyProfile}
    {betterSubject betterClassifier worseSubject worseClassifier : RawTerm 0}
    (betterDerivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) betterSubject betterClassifier)
    (worseDerivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) worseSubject worseClassifier) : Prop :=
  Conv betterSubject worseSubject
    ∧ betterDerivation.canonicalEvaluationCost ≤ worseDerivation.canonicalEvaluationCost

/-- **Cost-aware equivalence**: convertible AND exactly equal canonical
cost — the equivalence the NO-GO shows `Conv` is not. -/
def HasTypeDescPi.CostEquiv {profile : PolyProfile}
    {leftSubject leftClassifier rightSubject rightClassifier : RawTerm 0}
    (leftDerivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) leftSubject leftClassifier)
    (rightDerivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) rightSubject rightClassifier) : Prop :=
  Conv leftSubject rightSubject
    ∧ leftDerivation.canonicalEvaluationCost = rightDerivation.canonicalEvaluationCost

/-! ## Preorder / equivalence laws -/

/-- `Improves` is reflexive. -/
theorem HasTypeDescPi.Improves.refl {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (derivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) subject classifier) :
    derivation.Improves derivation :=
  ⟨Conv.refl subject, Nat.le_refl _⟩

/-- `Improves` is transitive (unconditional kernel `Conv.trans`). -/
theorem HasTypeDescPi.Improves.trans {profile : PolyProfile}
    {subjectA classifierA subjectB classifierB subjectC classifierC : RawTerm 0}
    {derivationA : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) subjectA classifierA}
    {derivationB : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) subjectB classifierB}
    {derivationC : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) subjectC classifierC}
    (firstLeg : derivationA.Improves derivationB)
    (secondLeg : derivationB.Improves derivationC) :
    derivationA.Improves derivationC :=
  ⟨Conv.trans firstLeg.1 secondLeg.1, Nat.le_trans firstLeg.2 secondLeg.2⟩

/-- `CostEquiv` is reflexive. -/
theorem HasTypeDescPi.CostEquiv.refl {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (derivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) subject classifier) :
    derivation.CostEquiv derivation :=
  ⟨Conv.refl subject, rfl⟩

/-- `CostEquiv` is symmetric. -/
theorem HasTypeDescPi.CostEquiv.sym {profile : PolyProfile}
    {leftSubject leftClassifier rightSubject rightClassifier : RawTerm 0}
    {leftDerivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) leftSubject leftClassifier}
    {rightDerivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) rightSubject rightClassifier}
    (equivalence : leftDerivation.CostEquiv rightDerivation) :
    rightDerivation.CostEquiv leftDerivation :=
  ⟨Conv.sym equivalence.1, equivalence.2.symm⟩

/-- `CostEquiv` is transitive. -/
theorem HasTypeDescPi.CostEquiv.trans {profile : PolyProfile}
    {subjectA classifierA subjectB classifierB subjectC classifierC : RawTerm 0}
    {derivationA : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) subjectA classifierA}
    {derivationB : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) subjectB classifierB}
    {derivationC : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) subjectC classifierC}
    (firstLeg : derivationA.CostEquiv derivationB)
    (secondLeg : derivationB.CostEquiv derivationC) :
    derivationA.CostEquiv derivationC :=
  ⟨Conv.trans firstLeg.1 secondLeg.1, firstLeg.2.trans secondLeg.2⟩

/-- **Cost transport**: cost-aware equivalence transports the canonical
cost — the property the NO-GO proves bare `Conv` lacks. -/
theorem HasTypeDescPi.CostEquiv.costEq {profile : PolyProfile}
    {leftSubject leftClassifier rightSubject rightClassifier : RawTerm 0}
    {leftDerivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) leftSubject leftClassifier}
    {rightDerivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) rightSubject rightClassifier}
    (equivalence : leftDerivation.CostEquiv rightDerivation) :
    leftDerivation.canonicalEvaluationCost = rightDerivation.canonicalEvaluationCost :=
  equivalence.2

/-- `CostEquiv` is exactly mutual improvement (the symmetrization of the
preorder): forward direction. -/
theorem HasTypeDescPi.CostEquiv.improves {profile : PolyProfile}
    {leftSubject leftClassifier rightSubject rightClassifier : RawTerm 0}
    {leftDerivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) leftSubject leftClassifier}
    {rightDerivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) rightSubject rightClassifier}
    (equivalence : leftDerivation.CostEquiv rightDerivation) :
    leftDerivation.Improves rightDerivation :=
  ⟨equivalence.1, Nat.le_of_eq equivalence.2⟩

/-- Reverse improvement from cost-aware equivalence. -/
theorem HasTypeDescPi.CostEquiv.improvesReverse {profile : PolyProfile}
    {leftSubject leftClassifier rightSubject rightClassifier : RawTerm 0}
    {leftDerivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) leftSubject leftClassifier}
    {rightDerivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) rightSubject rightClassifier}
    (equivalence : leftDerivation.CostEquiv rightDerivation) :
    rightDerivation.Improves leftDerivation :=
  ⟨Conv.sym equivalence.1, Nat.le_of_eq equivalence.2.symm⟩

/-- Mutual improvement is cost-aware equivalence (antisymmetry of the
preorder up to `CostEquiv`). -/
theorem HasTypeDescPi.CostEquiv.ofImprovesBoth {profile : PolyProfile}
    {leftSubject leftClassifier rightSubject rightClassifier : RawTerm 0}
    {leftDerivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) leftSubject leftClassifier}
    {rightDerivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) rightSubject rightClassifier}
    (forward : leftDerivation.Improves rightDerivation)
    (backward : rightDerivation.Improves leftDerivation) :
    leftDerivation.CostEquiv rightDerivation :=
  ⟨forward.1, Nat.le_antisymm forward.2 backward.2⟩

/-! ## ★ The normalizer is improvement-optimal -/

/-- The normal form re-typed at the SAME classifier (the unconditional
grown subject-reduction-star at the empty context). -/
def HasTypeDescPi.normalFormDerivation {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (derivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) subject classifier) :
    HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
      (RawTerm.normalize subject derivation.closedStronglyNormalizing) classifier :=
  HasTypeDescPi.subjectReductionStar
    (WfContextDescPi.emptyIsWellFormed (profile := profile))
    derivation
    (RawTerm.normalize_reducesTo subject derivation.closedStronglyNormalizing)

/-- The normal-form derivation has ZERO canonical cost (it types a
normal form; the zero-cost characterization closes). -/
theorem HasTypeDescPi.normalFormDerivation_cost_isZero {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (derivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) subject classifier) :
    derivation.normalFormDerivation.canonicalEvaluationCost = 0 :=
  RawTerm.normalizeCost_eq_zero_of_isStepNormalForm _
    (RawTerm.normalize_isStepNormalForm subject derivation.closedStronglyNormalizing)

/-- The normal-form derivation improves on the original. -/
theorem HasTypeDescPi.normalFormDerivation_improves {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (derivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) subject classifier) :
    derivation.normalFormDerivation.Improves derivation :=
  ⟨⟨RawTerm.normalize subject derivation.closedStronglyNormalizing,
     StepStar.refl _,
     RawTerm.normalize_reducesTo subject derivation.closedStronglyNormalizing⟩,
   by
     rw [derivation.normalFormDerivation_cost_isZero]
     exact Nat.zero_le _⟩

/-- ★ **The normalizer is improvement-OPTIMAL on its Conv class**: the
normal-form derivation improves on EVERY closed well-typed program whose
subject is convertible to the original — the cost-minimum of each Conv
class of closed well-typed programs is its normal form. -/
theorem HasTypeDescPi.normalFormDerivation_improvesAllConvertible {profile : PolyProfile}
    {subject classifier otherSubject otherClassifier : RawTerm 0}
    (derivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) subject classifier)
    (otherDerivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) otherSubject otherClassifier)
    (convertible : Conv subject otherSubject) :
    derivation.normalFormDerivation.Improves otherDerivation :=
  ⟨Conv.trans
     ⟨RawTerm.normalize subject derivation.closedStronglyNormalizing,
      StepStar.refl _,
      RawTerm.normalize_reducesTo subject derivation.closedStronglyNormalizing⟩
     convertible,
   by
     rw [derivation.normalFormDerivation_cost_isZero]
     exact Nat.zero_le _⟩

/-! ## ★ Decidability -/

/-- ★ The improvement preorder is DECIDABLE on closed well-typed
programs: `Conv` by normalize-and-compare (SN from typing), the cost
comparison as a `Nat` test. -/
def HasTypeDescPi.decideImproves {profile : PolyProfile}
    {betterSubject betterClassifier worseSubject worseClassifier : RawTerm 0}
    (betterDerivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) betterSubject betterClassifier)
    (worseDerivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) worseSubject worseClassifier) :
    Decidable (betterDerivation.Improves worseDerivation) :=
  @instDecidableAnd _ _
    (Conv.decidableOfStronglyNormalizing
      betterDerivation.closedStronglyNormalizing
      worseDerivation.closedStronglyNormalizing)
    (Nat.decLe _ _)

/-- ★ Cost-aware equivalence is DECIDABLE on closed well-typed
programs. -/
def HasTypeDescPi.decideCostEquiv {profile : PolyProfile}
    {leftSubject leftClassifier rightSubject rightClassifier : RawTerm 0}
    (leftDerivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) leftSubject leftClassifier)
    (rightDerivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) rightSubject rightClassifier) :
    Decidable (leftDerivation.CostEquiv rightDerivation) :=
  @instDecidableAnd _ _
    (Conv.decidableOfStronglyNormalizing
      leftDerivation.closedStronglyNormalizing
      rightDerivation.closedStronglyNormalizing)
    (Nat.decEq _ _)

/-! ## Non-vacuity — a concrete STRICT improvement -/

/-- The typed β-redex `(λx:Type@1. x)(Type@0)` at concrete levels. -/
def identityApplicationRedexDerivation (profile : PolyProfile) :
    HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
      (appCell (lamCell (universeCodeCell LevelExpr.lzero.lsucc .standard)
          (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
        (universeCodeCell .lzero .standard))
      (universeCodeCell LevelExpr.lzero.lsucc .standard) :=
  identityApplicationOnUniverseCode_hasTypeDescPi (profile := profile) .lzero .standard

/-- The redex's β-reduct `Type@0`, typed at the SAME classifier. -/
def identityApplicationReductDerivation (profile : PolyProfile) :
    HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
      (universeCodeCell .lzero .standard)
      (universeCodeCell LevelExpr.lzero.lsucc .standard) :=
  HasTypeDescPi.ofFormation
    (HasTypeDesc.universeFormation TypingContext.empty .lzero .standard)

/-- The reduct is a normal form (kernel evaluation on the concrete
cell). -/
theorem identityApplicationReduct_isStepNormalForm :
    RawTerm.isStepNormalForm
      (universeCodeCell LevelExpr.lzero .standard : RawTerm 0) :=
  RawTerm.reduceOnce_complete
    (rfl : RawTerm.reduceOnce
      (universeCodeCell LevelExpr.lzero .standard : RawTerm 0) = none)

/-- ★ **A concrete STRICT improvement**: the reduct improves on the
typed β-redex, and NOT conversely — the redex's nonzero canonical cost
(zero would make it normal, contradicting its β-step) against the
reduct's zero. -/
theorem identityApplicationReduct_strictlyImproves {profile : PolyProfile} :
    (identityApplicationReductDerivation profile).Improves
        (identityApplicationRedexDerivation profile)
      ∧ ¬ (identityApplicationRedexDerivation profile).Improves
            (identityApplicationReductDerivation profile) :=
  ⟨⟨Conv.sym
      ⟨universeCodeCell LevelExpr.lzero .standard,
       StepStar.trans
         (identityApplicationOnUniverseCode_betaReducesToArgument .lzero .standard)
         (StepStar.refl _),
       StepStar.refl _⟩,
    by
      rw [show (identityApplicationReductDerivation profile).canonicalEvaluationCost = 0 from
        RawTerm.normalizeCost_eq_zero_of_isStepNormalForm _
          identityApplicationReduct_isStepNormalForm]
      exact Nat.zero_le _⟩,
   fun improvement => by
     have reductCostZero :
         (identityApplicationReductDerivation profile).canonicalEvaluationCost = 0 :=
       RawTerm.normalizeCost_eq_zero_of_isStepNormalForm _
         identityApplicationReduct_isStepNormalForm
     have redexLeZero :
         (identityApplicationRedexDerivation profile).canonicalEvaluationCost ≤ 0 :=
       Nat.le_trans improvement.2 (Nat.le_of_eq reductCostZero)
     have redexCostZero :
         (identityApplicationRedexDerivation profile).canonicalEvaluationCost = 0 :=
       Nat.eq_zero_of_le_zero redexLeZero
     exact absurd
       (identityApplicationOnUniverseCode_betaReducesToArgument LevelExpr.lzero .standard)
       (RawTerm.isStepNormalForm_blocks_step
         (RawTerm.isStepNormalForm_of_normalizeCost_eq_zero _ redexCostZero) _)⟩

end FX1Poly.Typed
