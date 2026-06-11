import FX1Poly.Typed.CostAwareEquivalence

/-! # FX1Poly/Typed/OptimizationCell
    — ★ the first VERIFIED OPTIMIZATION CELL: a cost-decreasing extensional rewrite with certificates (OPT-0)

The meta-algorithmic demonstrator: an optimization is a CELL carrying
its own correctness — both certificates are kernel-checked fields, not
side conditions.  This is the interface every OPT-arc schema (fusion,
deforestation, memoization, ...) produces into, and the COST-4
`Improves` preorder is exactly where its cells land.

  * `OptimizationCell` — source and optimized programs typed at the
    SAME classifier (an optimization never changes the type), with the
    EXTENSIONAL certificate (`Conv` — same behavior) and the COST
    certificate (canonical cost no larger) as fields.
    `OptimizationCell.improves` bridges to the COST-4 preorder.
  * `HasTypeDescPi.canonicalEvaluationCost_eq_of_subjectEq` — cost is a
    function of the SUBJECT (Acc proof irrelevance) — the transport
    that makes cells COMPOSE.
  * `OptimizationCell.identity` / ★ `OptimizationCell.compose` — the
    pipeline algebra: cells compose along matching programs, and
    strictness propagates through composition from either leg
    (`compose_isStrict_ofFirst` / `_ofSecond`).
  * ★ `OptimizationCell.normalizeCell` — **the universal certified
    optimizer**: EVERY closed well-typed program carries a canonical
    optimization cell to its normal form, with zero optimized cost
    (`normalizeCell_optimizedCost_isZero`) — the COST-4
    improvement-optimality packaged as a cell factory.
  * ★ `betaRewriteCell` + `betaRewriteCell_isStrict` — the concrete
    demonstrator: the β-rewrite on the typed redex
    `(λx:Type@1. x)(Type@0)` as a STRICTLY cost-decreasing cell, every
    certificate enumerated and kernel-checked.

Honest scope: a cell certifies ONE rewrite's extensional safety and
cost direction; schema-level uniformity (one cell family per
optimization pattern) is OPT-2+, and cost-ordered termination of cell
rewriting is OPT-6.

Zero-axiom; gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core
open FX1Poly.Universe

/-! ## Cost is a function of the subject -/

/-- **Cost transport along subject equality**: the canonical evaluation
cost depends only on the SUBJECT — derivations, classifiers, and SN
witnesses are cost-irrelevant (`Acc` proof irrelevance).  The transport
that makes optimization cells compose. -/
theorem HasTypeDescPi.canonicalEvaluationCost_eq_of_subjectEq {profile : PolyProfile}
    {subjectA classifierA subjectB classifierB : RawTerm 0}
    (derivationA : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) subjectA classifierA)
    (derivationB : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) subjectB classifierB)
    (subjectsEq : subjectA = subjectB) :
    derivationA.canonicalEvaluationCost = derivationB.canonicalEvaluationCost := by
  subst subjectsEq
  rfl

/-! ## ★ The optimization cell -/

/-- ★ **A verified optimization cell**: source and optimized programs at
the SAME classifier, carrying the extensional certificate (same
behavior) and the cost certificate (no more expensive) as
kernel-checked FIELDS. -/
structure OptimizationCell (profile : PolyProfile) (classifier : RawTerm 0) where
  /-- The program being optimized. -/
  sourceSubject : RawTerm 0
  /-- The optimized program. -/
  optimizedSubject : RawTerm 0
  /-- The source is well-typed. -/
  sourceDerivation : HasTypeDescPi profile
    (TypingContext.empty : TypingContext profile 0) sourceSubject classifier
  /-- The optimized program is well-typed AT THE SAME TYPE. -/
  optimizedDerivation : HasTypeDescPi profile
    (TypingContext.empty : TypingContext profile 0) optimizedSubject classifier
  /-- EXTENSIONAL certificate: the rewrite preserves behavior. -/
  extensionalCertificate : Conv optimizedSubject sourceSubject
  /-- COST certificate: the rewrite does not increase canonical cost. -/
  costCertificate : optimizedDerivation.canonicalEvaluationCost
    ≤ sourceDerivation.canonicalEvaluationCost

/-- A cell's certificates are exactly a COST-4 improvement witness. -/
theorem OptimizationCell.improves {profile : PolyProfile} {classifier : RawTerm 0}
    (cell : OptimizationCell profile classifier) :
    cell.optimizedDerivation.Improves cell.sourceDerivation :=
  ⟨cell.extensionalCertificate, cell.costCertificate⟩

/-- A cell is STRICT when it genuinely lowers the cost. -/
def OptimizationCell.IsStrict {profile : PolyProfile} {classifier : RawTerm 0}
    (cell : OptimizationCell profile classifier) : Prop :=
  cell.optimizedDerivation.canonicalEvaluationCost
    < cell.sourceDerivation.canonicalEvaluationCost

/-! ## The pipeline algebra -/

/-- The trivial cell (no rewrite). -/
def OptimizationCell.identity {profile : PolyProfile} {classifier : RawTerm 0}
    {subject : RawTerm 0}
    (derivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) subject classifier) :
    OptimizationCell profile classifier where
  sourceSubject := subject
  optimizedSubject := subject
  sourceDerivation := derivation
  optimizedDerivation := derivation
  extensionalCertificate := Conv.refl subject
  costCertificate := Nat.le_refl _

/-- ★ **Optimization pipelines compose**: a cell out of the first cell's
optimized program composes into a cell from the first source to the
second optimized program — both certificates chain (the cost legs meet
through cost-transport along the matching subjects). -/
def OptimizationCell.compose {profile : PolyProfile} {classifier : RawTerm 0}
    (firstCell secondCell : OptimizationCell profile classifier)
    (linked : secondCell.sourceSubject = firstCell.optimizedSubject) :
    OptimizationCell profile classifier where
  sourceSubject := firstCell.sourceSubject
  optimizedSubject := secondCell.optimizedSubject
  sourceDerivation := firstCell.sourceDerivation
  optimizedDerivation := secondCell.optimizedDerivation
  extensionalCertificate :=
    Conv.trans secondCell.extensionalCertificate
      (by rw [linked]; exact firstCell.extensionalCertificate)
  costCertificate :=
    Nat.le_trans secondCell.costCertificate
      (Nat.le_trans
        (Nat.le_of_eq
          (HasTypeDescPi.canonicalEvaluationCost_eq_of_subjectEq
            secondCell.sourceDerivation firstCell.optimizedDerivation linked))
        firstCell.costCertificate)

/-- Strictness propagates through composition from the FIRST leg. -/
theorem OptimizationCell.compose_isStrict_ofFirst {profile : PolyProfile}
    {classifier : RawTerm 0}
    (firstCell secondCell : OptimizationCell profile classifier)
    (linked : secondCell.sourceSubject = firstCell.optimizedSubject)
    (firstStrict : firstCell.IsStrict) :
    (firstCell.compose secondCell linked).IsStrict :=
  Nat.lt_of_le_of_lt
    (Nat.le_trans secondCell.costCertificate
      (Nat.le_of_eq
        (HasTypeDescPi.canonicalEvaluationCost_eq_of_subjectEq
          secondCell.sourceDerivation firstCell.optimizedDerivation linked)))
    firstStrict

/-- Strictness propagates through composition from the SECOND leg. -/
theorem OptimizationCell.compose_isStrict_ofSecond {profile : PolyProfile}
    {classifier : RawTerm 0}
    (firstCell secondCell : OptimizationCell profile classifier)
    (linked : secondCell.sourceSubject = firstCell.optimizedSubject)
    (secondStrict : secondCell.IsStrict) :
    (firstCell.compose secondCell linked).IsStrict :=
  Nat.lt_of_lt_of_le
    (Nat.lt_of_lt_of_le secondStrict
      (Nat.le_of_eq
        (HasTypeDescPi.canonicalEvaluationCost_eq_of_subjectEq
          secondCell.sourceDerivation firstCell.optimizedDerivation linked)))
    firstCell.costCertificate

/-! ## ★ The universal certified optimizer -/

/-- ★ **The universal certified optimizer**: every closed well-typed
program carries a canonical optimization cell to its NORMAL FORM — the
COST-4 improvement-optimality packaged as a cell factory. -/
def OptimizationCell.normalizeCell {profile : PolyProfile} {classifier : RawTerm 0}
    {subject : RawTerm 0}
    (derivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) subject classifier) :
    OptimizationCell profile classifier where
  sourceSubject := subject
  optimizedSubject := RawTerm.normalize subject derivation.closedStronglyNormalizing
  sourceDerivation := derivation
  optimizedDerivation := derivation.normalFormDerivation
  extensionalCertificate := derivation.normalFormDerivation_improves.1
  costCertificate := derivation.normalFormDerivation_improves.2

/-- The universal optimizer's output costs ZERO — no cell over the same
program can do better. -/
theorem OptimizationCell.normalizeCell_optimizedCost_isZero {profile : PolyProfile}
    {classifier : RawTerm 0} {subject : RawTerm 0}
    (derivation : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0) subject classifier) :
    (OptimizationCell.normalizeCell derivation).optimizedDerivation.canonicalEvaluationCost
      = 0 :=
  derivation.normalFormDerivation_cost_isZero

/-! ## ★ The concrete demonstrator — a strict β-rewrite cell -/

/-- The typed β-redex's cost is NONZERO (zero would make it a normal
form, contradicting its β-step). -/
theorem identityApplicationRedex_cost_ne_zero {profile : PolyProfile} :
    (identityApplicationRedexDerivation profile).canonicalEvaluationCost ≠ 0 :=
  fun zeroCost =>
    absurd
      (identityApplicationOnUniverseCode_betaReducesToArgument LevelExpr.lzero .standard)
      (RawTerm.isStepNormalForm_blocks_step
        (RawTerm.isStepNormalForm_of_normalizeCost_eq_zero _ zeroCost) _)

/-- ★ **The first verified optimization cell**: the β-rewrite
`(λx:Type@1. x)(Type@0) ⤳ Type@0`, with every certificate enumerated —
both typings, the extensional `Conv`, and the cost direction. -/
def betaRewriteCell (profile : PolyProfile) :
    OptimizationCell profile (universeCodeCell LevelExpr.lzero.lsucc .standard) where
  sourceSubject :=
    appCell (lamCell (universeCodeCell LevelExpr.lzero.lsucc .standard)
        (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
      (universeCodeCell .lzero .standard)
  optimizedSubject := universeCodeCell LevelExpr.lzero .standard
  sourceDerivation := identityApplicationRedexDerivation profile
  optimizedDerivation := identityApplicationReductDerivation profile
  extensionalCertificate := (identityApplicationReduct_strictlyImproves (profile := profile)).1.1
  costCertificate := (identityApplicationReduct_strictlyImproves (profile := profile)).1.2

/-- ★ **The demonstrator is STRICT**: the β-rewrite genuinely lowers the
canonical cost (zero against provably nonzero). -/
theorem betaRewriteCell_isStrict {profile : PolyProfile} :
    (betaRewriteCell profile).IsStrict := by
  have reductCostZero :
      (identityApplicationReductDerivation profile).canonicalEvaluationCost = 0 :=
    RawTerm.normalizeCost_eq_zero_of_isStepNormalForm _
      identityApplicationReduct_isStepNormalForm
  show (identityApplicationReductDerivation profile).canonicalEvaluationCost
    < (identityApplicationRedexDerivation profile).canonicalEvaluationCost
  rw [reductCostZero]
  exact Nat.pos_of_ne_zero (identityApplicationRedex_cost_ne_zero (profile := profile))

end FX1Poly.Typed
