import FX1Poly.Core.CostBound
import FX1Poly.Typed.ClosedStronglyNormalizing
import FX1Poly.Typed.OpenStronglyNormalizingUnconditional
import FX1Poly.Typed.TypedLambdaDerivations

/-! # FX1Poly/Typed/WellTypedCostCalculable
    — ★ EVERY WELL-TYPED FX PROGRAM HAS CALCULABLE COST (COST-3 brick 5)

The typed packaging of the kernel cost semantics (bricks 1–4): the shipped
typed-SN theorems feed the cost machinery with ZERO glue, because
`StepStar.IsStronglyNormalizing` IS `Acc StepStar.StepSuccessor`
definitionally — exactly the accessibility `costBound` and `normalizeCost`
recurse over.

  * ★ `HasTypeDescPi.costCalculator` — every CLOSED well-typed kernel
    program carries a computable worst-case evaluation bound (SN supplied
    by `closedStronglyNormalizing`, the unconditional SN-043 closed
    capstone).  `costCalculator_isSound`: no reduction chain from the
    program, under ANY strategy, exceeds it.
  * ★ `HasTypeDescPi.canonicalEvaluationCost` — the EXACT cost of the
    canonical strategy: a genuine counted chain of exactly that length
    reaching THE normal form (`canonicalEvaluationCost_isExact`), never
    exceeding the worst case (`canonicalEvaluationCost_le_costCalculator`).
  * The OPEN twins (`costCalculatorOpen` / `canonicalEvaluationCostOpen`)
    over any well-formed context, via `stronglyNormalizingOfWfContextDesc`
    (the `WfContextDesc` hypothesis is genuinely external — context
    validity provably does NOT follow from the derivation).
  * ★ `wellTypedClosedProgram_costIsCalculable` — the bundle headline:
    soundness + attained exactness in one statement, the §6.3 Dim-13
    promise at the KERNEL ("complexity is opt-in" rests on cost being
    semantically real for every well-typed program).
  * Non-vacuity: the concrete typed β-redex
    `(λ(x : Type@(e+1)). x) (Type@e)` (a shipped `piElim` derivation) has
    POSITIVE calculated cost — its β-step is counted by the calculator.

## Honest scope boundary

As at the graded layer (COST-1): the cost is computed FROM THE TERM (the
worst-case bound by reduction-graph search, the exact cost by instrumented
evaluation), not read off the types.  What typing adds is TOTALITY: the SN
theorem guarantees the calculators are defined on every well-typed program.

Zero-axiom; gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core
open FX1Poly.Universe
open StepStar

/-! ## ★ The closed-program cost calculator -/

/-- ★ **The worst-case cost calculator for closed well-typed programs**:
typing supplies strong normalization (`closedStronglyNormalizing`), the
kernel bound (brick 4) does the rest. -/
def HasTypeDescPi.costCalculator {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (derivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) subject classifier) : Nat :=
  RawTerm.costBound subject derivation.closedStronglyNormalizing

/-- The calculator is SOUND: no counted reduction chain from a closed
well-typed program — under ANY strategy — exceeds it. -/
theorem HasTypeDescPi.costCalculator_isSound {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (derivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) subject classifier)
    {steps : Nat} {target : RawTerm 0}
    (chain : StepStarN steps subject target) :
    steps ≤ derivation.costCalculator :=
  RawTerm.costBound_isSound derivation.closedStronglyNormalizing chain

/-- ★ **The exact canonical-evaluation cost** of a closed well-typed
program: the step count of the shipped kernel normalizer's own path. -/
def HasTypeDescPi.canonicalEvaluationCost {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (derivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) subject classifier) : Nat :=
  RawTerm.normalizeCost subject derivation.closedStronglyNormalizing

/-- The canonical cost is EXACT: a genuine counted chain of exactly that
length from the program to THE normal form — attained, not just bounded. -/
theorem HasTypeDescPi.canonicalEvaluationCost_isExact {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (derivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) subject classifier) :
    StepStarN derivation.canonicalEvaluationCost subject
      (RawTerm.normalize subject derivation.closedStronglyNormalizing) :=
  RawTerm.normalizeCost_isExact subject derivation.closedStronglyNormalizing

/-- The sandwich: the canonical strategy's exact cost never exceeds the
worst-case calculator. -/
theorem HasTypeDescPi.canonicalEvaluationCost_le_costCalculator
    {profile : PolyProfile} {subject classifier : RawTerm 0}
    (derivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) subject classifier) :
    derivation.canonicalEvaluationCost ≤ derivation.costCalculator :=
  RawTerm.normalizeCost_le_costBound subject derivation.closedStronglyNormalizing

/-! ## The open-program twins (well-formed contexts) -/

/-- The worst-case cost calculator for OPEN well-typed programs over a
well-formed context (`WfContextDesc` is genuinely external — it provably
does not follow from the derivation). -/
def HasTypeDescPi.costCalculatorOpen {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (derivation : HasTypeDescPi profile context subject classifier) : Nat :=
  RawTerm.costBound subject
    (derivation.stronglyNormalizingOfWfContextDesc contextWellFormed)

/-- Open-program soundness: no counted chain from an open well-typed
program over a well-formed context exceeds its calculator. -/
theorem HasTypeDescPi.costCalculatorOpen_isSound {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (derivation : HasTypeDescPi profile context subject classifier)
    {steps : Nat} {target : RawTerm scope}
    (chain : StepStarN steps subject target) :
    steps ≤ derivation.costCalculatorOpen contextWellFormed :=
  RawTerm.costBound_isSound
    (derivation.stronglyNormalizingOfWfContextDesc contextWellFormed) chain

/-- The exact canonical-evaluation cost of an open well-typed program. -/
def HasTypeDescPi.canonicalEvaluationCostOpen {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (derivation : HasTypeDescPi profile context subject classifier) : Nat :=
  RawTerm.normalizeCost subject
    (derivation.stronglyNormalizingOfWfContextDesc contextWellFormed)

/-- Open-program exactness: the canonical cost is attained by a genuine
counted chain to the computed normal form. -/
theorem HasTypeDescPi.canonicalEvaluationCostOpen_isExact {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (derivation : HasTypeDescPi profile context subject classifier) :
    StepStarN (derivation.canonicalEvaluationCostOpen contextWellFormed) subject
      (RawTerm.normalize subject
        (derivation.stronglyNormalizingOfWfContextDesc contextWellFormed)) :=
  RawTerm.normalizeCost_isExact subject
    (derivation.stronglyNormalizingOfWfContextDesc contextWellFormed)

/-! ## ★ The headline bundle -/

/-- ★ **Every closed well-typed FX kernel program has calculable cost**
(the §6.3 Dim-13 promise at the kernel): a computable sound worst-case
bound for EVERY strategy, AND a computable exact canonical-evaluation cost
attained by a genuine counted chain to THE normal form.  What this does NOT
claim: that the cost can be read off the types — the calculators compute
from the term; typing contributes TOTALITY (the SN guarantee that they are
defined). -/
theorem wellTypedClosedProgram_costIsCalculable {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (derivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) subject classifier) :
    (∀ {steps : Nat} {target : RawTerm 0},
        StepStarN steps subject target → steps ≤ derivation.costCalculator)
      ∧ StepStarN derivation.canonicalEvaluationCost subject
          (RawTerm.normalize subject derivation.closedStronglyNormalizing) :=
  ⟨fun chain => derivation.costCalculator_isSound chain,
   derivation.canonicalEvaluationCost_isExact⟩

/-! ## Non-vacuity — a concrete typed β-redex has positive calculated cost -/

/-- **The calculator counts a real program's real work**: the shipped typed
β-redex `(λ(x : Type@(e+1)). x) (Type@e)` (a concrete closed `piElim`
derivation) has POSITIVE worst-case cost — its β-step is a 1-chain the
calculator must bound. -/
theorem identityApplication_costCalculator_isPositive
    {profile : PolyProfile} (levelExpr : LevelExpr) (flag : UniverseFlag) :
    1 ≤ (identityApplicationOnUniverseCode_hasTypeDescPi
          (profile := profile) levelExpr flag).costCalculator :=
  (identityApplicationOnUniverseCode_hasTypeDescPi
      (profile := profile) levelExpr flag).costCalculator_isSound
    (StepStarN.transN
      (identityApplicationOnUniverseCode_betaReducesToArgument levelExpr flag)
      (StepStarN.reflN (universeCodeCell levelExpr flag)))

end FX1Poly.Typed
