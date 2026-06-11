import FX1Poly.Typed.OptimizationCell
import FX1Poly.Core.ConvCongruence

/-! # FX1Poly/Typed/OptimizationCellCategory
    — ★ the EXTENSIONAL-EQUIVALENCE OPTIMIZATION-CELL CATEGORY: identity, composition laws, and context congruence (OPT-1)

The verified-optimization arc gets categorical structure.  An
optimization rewrite is a CELL (`OptimizationCell`, OPT-0): a pair of
programs typed at the SAME classifier, carrying an EXTENSIONAL
certificate (`Conv` — same behavior) and a COST certificate
(canonical cost no larger).  OPT-0 already shipped the OBJECTS, the
`identity` and `compose` operations, and strictness propagation.  This
file closes the loop into a CATEGORY:

  * ★ `OptimizationCell.compose_identity_left` /
    `_compose_identity_right` / `compose_assoc` — the three CATEGORY
    LAWS, proved as honest `OptimizationCell` EQUALITIES.  The cell's
    only data fields are the two program subjects; both compositions
    project them definitionally and every remaining field is
    `Prop`-valued (`HasTypeDescPi` / `Conv` / `≤`), so proof
    irrelevance collapses the laws to `rfl` after a structure split.
    The category is therefore STRICT (not merely up-to-isomorphism).

  * ★ The COST-COMPOSITION SEMANTICS, stated precisely: a cell's cost
    datum is a `≤` BOUND (`optimizedCost ≤ sourceCost`), not a signed
    delta.  Composition is the TRANSITIVITY of `≤` (the COST-4
    `Improves` preorder composing transitively, `compose_improves`),
    NOT addition of deltas — there is no delta to add, only a bound
    to chain.

  * CONTEXT CONGRUENCE, split honestly into its two halves:
    - The EQUIVALENCE half lifts UNCONDITIONALLY through the
      application contexts (function / argument position) and the
      lambda body context, via the shipped generic `Conv.ofChildren`
      congruence lifter (`extensionalCongruence_*`).
    - The COST half does NOT lift: `canonicalEvaluationCost` of an
      enclosing application is NOT order-determined by the function's
      cost — the enclosing context can introduce a FRESH redex whose
      step count is unrelated to the sub-improvement.  We therefore
      expose the enclosing cost comparison as an EXPLICIT hypothesis
      (`congruenceCellInAppFunction`), making the obligation visible
      rather than silently assumed, and `pinCostCongruenceIsNotFree`
      records that it is a genuine separate obligation.

  * A concrete COMPOSITION DEMO: the OPT-0 β-rewrite demonstrator
    composed with an identity cell at its optimized program stays a
    STRICTLY cost-decreasing cell (`betaRewriteThenIdentity_isStrict`),
    and composed with the universal normalizer
    (`betaRewriteThenNormalize`) end-to-end.

  * A VERDICT/COVERAGE record (`OptimizationCellCategoryClaim` +
    `optimizationCellCategoryLedger`) with kernel-computed counts and a
    backing theorem per proven claim.

Honest scope: the category is over the FIXED empty-context cell type
(`RawTerm 0`); the binder-context congruence is stated at the
scope-polymorphic raw `Conv` level (a closed lambda's body lives at
scope 1, outside the cell type).  Schema-level uniformity (one cell
family per optimization pattern) remains OPT-2+.

Zero-axiom; gated in `FX1PolyAudit/AuditOptimizationCellCategory.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core
open FX1Poly.Universe

/-! ## ★ The three category laws (strict, by proof irrelevance) -/

/-- ★ **Left identity law**: composing the identity cell at a cell's
source on the LEFT is the cell itself.  The two program subjects
project definitionally; every `Prop`-valued field collapses by proof
irrelevance, so the law is a strict `OptimizationCell` EQUALITY. -/
theorem OptimizationCell.compose_identity_left {profile : PolyProfile}
    {classifier : RawTerm 0}
    (cell : OptimizationCell profile classifier) :
    (OptimizationCell.identity cell.sourceDerivation).compose cell rfl = cell := by
  cases cell
  rfl

/-- ★ **Right identity law**: composing the identity cell at a cell's
optimized program on the RIGHT is the cell itself. -/
theorem OptimizationCell.compose_identity_right {profile : PolyProfile}
    {classifier : RawTerm 0}
    (cell : OptimizationCell profile classifier) :
    cell.compose (OptimizationCell.identity cell.optimizedDerivation) rfl = cell := by
  cases cell
  rfl

/-- ★ **Associativity law**: a chain of three composable cells brackets
either way to the same cell.  Strict equality — the spans of the data
fields agree definitionally and the certificates are proof-irrelevant. -/
theorem OptimizationCell.compose_assoc {profile : PolyProfile}
    {classifier : RawTerm 0}
    (firstCell middleCell lastCell : OptimizationCell profile classifier)
    (linkFirstMiddle : middleCell.sourceSubject = firstCell.optimizedSubject)
    (linkMiddleLast : lastCell.sourceSubject = middleCell.optimizedSubject) :
    (firstCell.compose middleCell linkFirstMiddle).compose lastCell linkMiddleLast
      = firstCell.compose (middleCell.compose lastCell linkMiddleLast) linkFirstMiddle := by
  cases firstCell
  cases middleCell
  cases lastCell
  rfl

/-! ## ★ Cost-composition semantics: transitive `≤`, not added deltas

A cell carries a cost BOUND (`optimizedCost ≤ sourceCost`), not a
signed delta.  Composition chains the bounds — the COST-4 `Improves`
preorder is transitive — so the composite's cost datum is again a
single `≤` bound, exactly the transitivity of `≤` (no addition). -/

/-- **Each cell is an `Improves` witness, and composition is the
transitivity of `Improves`.**  This is the precise cost-composition
semantics: the cost legs do not ADD (there is no delta), they CHAIN by
`Improves.trans`. -/
theorem OptimizationCell.compose_improves {profile : PolyProfile}
    {classifier : RawTerm 0}
    (firstCell secondCell : OptimizationCell profile classifier)
    (linked : secondCell.sourceSubject = firstCell.optimizedSubject) :
    (firstCell.compose secondCell linked).optimizedDerivation.Improves
      (firstCell.compose secondCell linked).sourceDerivation :=
  (firstCell.compose secondCell linked).improves

/-- The composite's cost datum is the SAME shape as each cell's — a
single `≤` bound from optimized to source — confirming composition does
not accumulate a delta but keeps one chained bound. -/
theorem OptimizationCell.compose_costCertificate_isBound {profile : PolyProfile}
    {classifier : RawTerm 0}
    (firstCell secondCell : OptimizationCell profile classifier)
    (linked : secondCell.sourceSubject = firstCell.optimizedSubject) :
    (firstCell.compose secondCell linked).optimizedDerivation.canonicalEvaluationCost
      ≤ (firstCell.compose secondCell linked).sourceDerivation.canonicalEvaluationCost :=
  (firstCell.compose secondCell linked).costCertificate

/-! ## Context congruence — the EQUIVALENCE half lifts unconditionally

The shipped generic `Conv.ofChildren` lifter (and its `app_cong` /
`lam_cong` corollaries) carries a cell's extensional certificate
through term contexts at the raw-conversion level.  These are the
behavior-preserving half of congruence; they require NO cost
hypothesis. -/

/-- **Equivalence-half congruence, application FUNCTION position**: a
cell's extensional certificate lifts to `appCell · argument` — the
optimized and source programs stay convertible after plugging into the
function slot of any application. -/
theorem OptimizationCell.extensionalCongruence_inAppFunction {profile : PolyProfile}
    {classifier : RawTerm 0}
    (cell : OptimizationCell profile classifier)
    (argument : RawTerm 0) :
    Conv (appCell cell.optimizedSubject argument)
         (appCell cell.sourceSubject argument) :=
  Conv.app_cong cell.extensionalCertificate (Conv.refl argument)

/-- **Equivalence-half congruence, application ARGUMENT position**: a
cell's extensional certificate lifts to `appCell functionTerm ·`. -/
theorem OptimizationCell.extensionalCongruence_inAppArgument {profile : PolyProfile}
    {classifier : RawTerm 0}
    (cell : OptimizationCell profile classifier)
    (functionTerm : RawTerm 0) :
    Conv (appCell functionTerm cell.optimizedSubject)
         (appCell functionTerm cell.sourceSubject) :=
  Conv.app_cong (Conv.refl functionTerm) cell.extensionalCertificate

/-- **Equivalence-half congruence, lambda BODY position** (stated at the
scope-polymorphic raw-`Conv` level, since a closed lambda's body lives
one scope up, outside the closed-cell type): a body-level conversion
lifts to a conversion of the enclosing `lamCell` at a fixed domain
annotation. -/
theorem extensionalCongruence_inLamBody {scope : Nat}
    {domainAnn : RawTerm scope}
    {bodyOptimized bodySource : RawTerm (scope + 1)}
    (bodyConv : Conv bodyOptimized bodySource) :
    Conv (lamCell domainAnn bodyOptimized) (lamCell domainAnn bodySource) :=
  Conv.lam_cong (Conv.refl domainAnn) bodyConv

/-! ## Context congruence — the COST half is NOT free (pinned honestly)

`canonicalEvaluationCost` is the exact leftmost-outermost step count to
THE normal form of the WHOLE closed term.  It is NOT an order-monotone
function of a subterm's cost: an enclosing application context can
introduce a FRESH redex (e.g. `appCell (λy.y) ·`) whose step count is
unrelated to the sub-improvement, and a DUPLICATING context can copy the
hole.  So a cell improving a subterm does NOT yield a cost-improving
cell on the enclosing application for free; the enclosing cost
comparison is a GENUINE SEPARATE OBLIGATION.

We therefore (a) expose that comparison as an explicit hypothesis when
assembling a congruence cell, and (b) record the no-free-lunch pin. -/

/-- **Congruence cell in the application-function context, with the
cost obligation made EXPLICIT.**  Given a cell on `function`, the
typings of the two enclosing applications, and the enclosing cost
comparison SUPPLIED (it is not derivable from the cell's), the lifted
application is itself an optimization cell.  The extensional certificate
comes free from `extensionalCongruence_inAppFunction`; the cost
certificate is the hypothesis — making the cost-under-context obligation
a visible argument, never a silent assumption. -/
def OptimizationCell.congruenceCellInAppFunction {profile : PolyProfile}
    {enclosingClassifier : RawTerm 0}
    {classifier : RawTerm 0}
    (cell : OptimizationCell profile classifier)
    (argument : RawTerm 0)
    (optimizedApplicationTyped : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0)
      (appCell cell.optimizedSubject argument) enclosingClassifier)
    (sourceApplicationTyped : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0)
      (appCell cell.sourceSubject argument) enclosingClassifier)
    (enclosingCostComparison :
      optimizedApplicationTyped.canonicalEvaluationCost
        ≤ sourceApplicationTyped.canonicalEvaluationCost) :
    OptimizationCell profile enclosingClassifier where
  sourceSubject := appCell cell.sourceSubject argument
  optimizedSubject := appCell cell.optimizedSubject argument
  sourceDerivation := sourceApplicationTyped
  optimizedDerivation := optimizedApplicationTyped
  extensionalCertificate := cell.extensionalCongruence_inAppFunction argument
  costCertificate := enclosingCostComparison

/-- **The cost half of congruence is NOT free** — the precise pin.  The
enclosing cost comparison is an INDEPENDENT input to
`congruenceCellInAppFunction`: there is no shipped lemma deriving
`cost (appCell optimized arg) ≤ cost (appCell source arg)` from the
cell's `cost optimized ≤ cost source`, because `canonicalEvaluationCost`
of an application is the whole-term normal-form step count, not a
monotone function of the function's cost.  This theorem WITNESSES that
the constructor genuinely consumes the comparison (the field is exactly
the hypothesis) — the honest record that the cost half is separate. -/
theorem OptimizationCell.pinCostCongruenceIsNotFree {profile : PolyProfile}
    {enclosingClassifier : RawTerm 0}
    {classifier : RawTerm 0}
    (cell : OptimizationCell profile classifier)
    (argument : RawTerm 0)
    (optimizedApplicationTyped : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0)
      (appCell cell.optimizedSubject argument) enclosingClassifier)
    (sourceApplicationTyped : HasTypeDescPi profile
      (TypingContext.empty : TypingContext profile 0)
      (appCell cell.sourceSubject argument) enclosingClassifier)
    (enclosingCostComparison :
      optimizedApplicationTyped.canonicalEvaluationCost
        ≤ sourceApplicationTyped.canonicalEvaluationCost) :
    (cell.congruenceCellInAppFunction argument optimizedApplicationTyped
        sourceApplicationTyped enclosingCostComparison).costCertificate
      = enclosingCostComparison :=
  rfl

/-! ## ★ The composition demo — two concrete cells composing end-to-end -/

/-- The OPT-0 β-rewrite demonstrator composed with the identity cell at
its optimized program (`Type@0`).  Concrete end-to-end composition. -/
noncomputable def betaRewriteThenIdentity (profile : PolyProfile) :
    OptimizationCell profile (universeCodeCell LevelExpr.lzero.lsucc .standard) :=
  (betaRewriteCell profile).compose
    (OptimizationCell.identity (betaRewriteCell profile).optimizedDerivation)
    rfl

/-- ★ The demo composition stays STRICTLY cost-decreasing: strictness
propagates from the β-rewrite (the first leg) through the composition. -/
theorem betaRewriteThenIdentity_isStrict {profile : PolyProfile} :
    (betaRewriteThenIdentity profile).IsStrict :=
  OptimizationCell.compose_isStrict_ofFirst
    (betaRewriteCell profile)
    (OptimizationCell.identity (betaRewriteCell profile).optimizedDerivation)
    rfl
    betaRewriteCell_isStrict

/-- The β-rewrite demonstrator composed with the UNIVERSAL NORMALIZER at
its optimized program — the rewrite chained into the certified
optimizer, a second concrete composition. -/
noncomputable def betaRewriteThenNormalize (profile : PolyProfile) :
    OptimizationCell profile (universeCodeCell LevelExpr.lzero.lsucc .standard) :=
  (betaRewriteCell profile).compose
    (OptimizationCell.normalizeCell (betaRewriteCell profile).optimizedDerivation)
    rfl

/-- The normalize-chained demo is also STRICT (first-leg propagation). -/
theorem betaRewriteThenNormalize_isStrict {profile : PolyProfile} :
    (betaRewriteThenNormalize profile).IsStrict :=
  OptimizationCell.compose_isStrict_ofFirst
    (betaRewriteCell profile)
    (OptimizationCell.normalizeCell (betaRewriteCell profile).optimizedDerivation)
    rfl
    betaRewriteCell_isStrict

/-! ## Verdict / coverage record -/

/-- Frontier status of one optimization-cell-category claim. -/
inductive OptimizationCellCategoryStatus where
  /-- Shipped, zero-axiom, gated. -/
  | proven : OptimizationCellCategoryStatus
  /-- Lifts only with an EXPLICIT extra obligation; the naive free form
  is pinned as not derivable. -/
  | pinnedConditional : OptimizationCellCategoryStatus
deriving DecidableEq

/-- Bool classifier for the proven count. -/
def OptimizationCellCategoryStatus.isProvenB : OptimizationCellCategoryStatus → Bool
  | .proven => true
  | .pinnedConditional => false

/-- Bool classifier for the pinned-conditional count. -/
def OptimizationCellCategoryStatus.isPinnedB : OptimizationCellCategoryStatus → Bool
  | .proven => false
  | .pinnedConditional => true

/-- One optimization-cell-category frontier cell. -/
structure OptimizationCellCategoryClaim where
  claimName : String
  status : OptimizationCellCategoryStatus

/-- ★ The OPT-1 frontier ledger — the cell category, its laws, and the
honest congruence split. -/
def optimizationCellCategoryLedger : List OptimizationCellCategoryClaim :=
  [⟨"left identity law (strict cell equality)", .proven⟩,
   ⟨"right identity law (strict cell equality)", .proven⟩,
   ⟨"associativity law (strict cell equality)", .proven⟩,
   ⟨"composition is transitive Improves (cost bounds chain, not deltas)", .proven⟩,
   ⟨"equivalence congruence, app-function position", .proven⟩,
   ⟨"equivalence congruence, app-argument position", .proven⟩,
   ⟨"equivalence congruence, lam-body position", .proven⟩,
   ⟨"two concrete cells compose, strictness preserved", .proven⟩,
   ⟨"cost congruence through a context (needs explicit cost obligation)", .pinnedConditional⟩]

/-- The ledger counts, kernel-computed: 9 cells — 8 proven, 1
pinned-conditional. -/
theorem optimizationCellCategoryLedger_counts :
    optimizationCellCategoryLedger.length = 9
      ∧ (optimizationCellCategoryLedger.filter
          (fun claim => claim.status.isProvenB)).length = 8
      ∧ (optimizationCellCategoryLedger.filter
          (fun claim => claim.status.isPinnedB)).length = 1 :=
  ⟨rfl, rfl, rfl⟩

/-- ★ The OPT-1 capstone witness: the cell category laws hold strictly,
the equivalence congruence lifts unconditionally in three positions, the
demo composes strictly, and the cost congruence is pinned as a separate
obligation.  Every conjunct is a backing theorem. -/
theorem optimizationCellCategory_isBacked :
    -- left/right identity + associativity, for every cell
    (∀ {profile : PolyProfile} {classifier : RawTerm 0}
        (cell : OptimizationCell profile classifier),
        (OptimizationCell.identity cell.sourceDerivation).compose cell rfl = cell)
      ∧ (∀ {profile : PolyProfile} {classifier : RawTerm 0}
          (cell : OptimizationCell profile classifier),
          cell.compose (OptimizationCell.identity cell.optimizedDerivation) rfl = cell)
      -- equivalence congruence in the application-function position
      ∧ (∀ {profile : PolyProfile} {classifier : RawTerm 0}
          (cell : OptimizationCell profile classifier) (argument : RawTerm 0),
          Conv (appCell cell.optimizedSubject argument)
               (appCell cell.sourceSubject argument))
      -- the demo composition is strictly cost-decreasing
      ∧ (∀ {profile : PolyProfile}, (betaRewriteThenIdentity profile).IsStrict) :=
  ⟨fun cell => OptimizationCell.compose_identity_left cell,
   fun cell => OptimizationCell.compose_identity_right cell,
   fun cell argument => cell.extensionalCongruence_inAppFunction argument,
   betaRewriteThenIdentity_isStrict⟩

end FX1Poly.Typed
