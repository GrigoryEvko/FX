import FX1Poly.Core.Metatheory.Reducibility.Candidates.CarrierCombinatorTable
import FX1Poly.Core.Metatheory.Reducibility.Candidates.ProjectionPairCandidate

/-! # FX1Poly/Core/CarrierModelAssembler
    — `CarrierCombinator.assembleModel`: the Σ-projection model assembler + its obligation-aware interface

`CarrierCombinator.assemble` (`CarrierCombinatorTable.lean`) assigns the NF-value carrier-aware candidate to
every carrier-aware former — including `pairLike` (`carrierAwarePairCandidate`).  That candidate records each
component only at NORMAL pairs, so the `fst` / `snd` reach-conditioned residues cannot discharge for FUNCTION
(Π) component carriers (the Ω-fork; see `ProjectionPairCandidate.lean`).

`assembleModel` is the model-viable replacement: identical to `assemble` EXCEPT the `pairLike` arm assigns the
PROJECTION-based Girard candidate `projectionPairCandidate` (forward-correct, head-expansion-closed,
Ω-fork-free).  `coproductLike` / `equivLike` keep their NF-value carrier-aware candidates (their match-frame /
equiv strengthenings are separate follow-ups), so `assembleModel` is the correct INTERMEDIATE for the Σ-only
model swap: the bounded reducibility inductive's `dataFlatCarrierAware` arm stores `combinator.assembleModel`
in place of `combinator.assemble`, and the bounded metatheory dispatches the `dataFlatCarrierAware` case through
the obligation-aware interface lemmas below.

Because `projectionPairCandidate`'s validity / head-expansion REQUIRE `CarrierObligations` on the two component
carriers (the NF-value `dataTaitCandidate` arms need NOTHING), the interface lemmas thread `CarrierObligations`
uniformly — used by the `pairLike` arm, ignored by the `coproductLike` / `equivLike` arms.  At the bounded arm's
use site the component reducibles supply the obligations via `boundedTypeCarrierObligations`.

## Zero-axiom verification

Each interface lemma is `cases combinator` dispatching to the per-candidate theorem — `projectionPairCandidate_*`
(obligation-fed) for `pairLike`, the shipped `carrierAwareEither/EquivCandidate_*` (or `dataTaitCandidate.*`,
since each is a `dataTaitCandidate`) for the other two.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated by the `FX1Poly.Core` namespace sweep in
`FX1PolyAudit/`.
-/

namespace FX1Poly.Core

open StepStar

/-- **The Σ-projection model assembler.**  Identical to `CarrierCombinator.assemble` except `pairLike` assigns
the projection-based Girard candidate `projectionPairCandidate` (the model-viable, Ω-fork-free Σ candidate);
`coproductLike` / `equivLike` keep their NF-value carrier-aware candidates.  The candidate the bounded
reducibility inductive's `dataFlatCarrierAware` arm stores after the Σ swap. -/
def CarrierCombinator.assembleModel {scope : Nat} :
    CarrierCombinator → (RawTerm scope → Prop) → (RawTerm scope → Prop) → (RawTerm scope → Prop)
  | .pairLike, firstCandidate, secondCandidate =>
      projectionPairCandidate firstCandidate secondCandidate
  | .coproductLike, firstCandidate, secondCandidate =>
      carrierAwareEitherCandidate firstCandidate secondCandidate
  | .equivLike, firstCandidate, secondCandidate =>
      carrierAwareEquivCandidate firstCandidate secondCandidate

/-- **The model-assembled candidate is a Girard reducibility candidate**, given the component carriers'
reducibility candidacy — per-tag dispatch (`pairLike` → the minimized projection validity, the other two → their
NF-value candidate's own validity).  Needs only `IsReducibilityCandidate` on each component (NOT the full
`CarrierObligations`): this is exactly the interface the generic bounded candidacy site
(`ReducibleTypeStepBounded.isReducibilityCandidate`, whose induction IH supplies component candidacy but not
member weak-head expansion) can call. -/
theorem CarrierCombinator.assembleModel_isReducibilityCandidate {scope : Nat} (combinator : CarrierCombinator)
    (firstCandidate secondCandidate : RawTerm scope → Prop)
    (firstCandidateIsCandidate : IsReducibilityCandidate firstCandidate)
    (secondCandidateIsCandidate : IsReducibilityCandidate secondCandidate) :
    IsReducibilityCandidate (combinator.assembleModel firstCandidate secondCandidate) := by
  cases combinator
  · exact projectionPairCandidate_isReducibilityCandidate firstCandidateIsCandidate secondCandidateIsCandidate
  · exact carrierAwareEitherCandidate_isReducibilityCandidate firstCandidate secondCandidate
  · exact carrierAwareEquivCandidate_isReducibilityCandidate firstCandidate secondCandidate

/-- **The model-assembled candidate is head-expansion-closed** (the Π-codomain arm property), given the
component carriers' member weak-head expansion — per-tag dispatch.  The `pairLike` projection arm needs only the
two components' member-weak-head-expansion functions (NOT full `CarrierObligations`); the other two arms ignore
them (their NF-value `dataTaitCandidate` head-expansion is unconditional). -/
theorem CarrierCombinator.assembleModel_headExpansionClosed {scope : Nat} (combinator : CarrierCombinator)
    (firstCandidate secondCandidate : RawTerm scope → Prop)
    (firstWeakHeadExpansion : ∀ {source reduct : RawTerm scope},
        WeakHeadStep source reduct → IsStronglyNormalizing source → firstCandidate reduct →
        firstCandidate source)
    (secondWeakHeadExpansion : ∀ {source reduct : RawTerm scope},
        WeakHeadStep source reduct → IsStronglyNormalizing source → secondCandidate reduct →
        secondCandidate source) :
    HeadExpansionClosed (combinator.assembleModel firstCandidate secondCandidate) := by
  cases combinator
  · exact projectionPairCandidate_headExpansionClosed firstWeakHeadExpansion secondWeakHeadExpansion
  · exact carrierAwareEitherCandidate_headExpansionClosed firstCandidate secondCandidate
  · exact carrierAwareEquivCandidate_headExpansionClosed firstCandidate secondCandidate

/-- **The model-assembled candidate is congruent in its carriers** (the `deterministic` finisher) — needs no
obligations (pointwise transport), per-tag dispatch. -/
theorem CarrierCombinator.assembleModel_congr {scope : Nat} (combinator : CarrierCombinator)
    {firstCandidate1 firstCandidate2 secondCandidate1 secondCandidate2 : RawTerm scope → Prop}
    (firstIff : PointwiseIff firstCandidate1 firstCandidate2)
    (secondIff : PointwiseIff secondCandidate1 secondCandidate2) :
    PointwiseIff (combinator.assembleModel firstCandidate1 secondCandidate1)
      (combinator.assembleModel firstCandidate2 secondCandidate2) := by
  cases combinator
  · exact projectionPairCandidate_congr firstIff secondIff
  · exact carrierAwareEitherCandidate_congr firstIff secondIff
  · exact carrierAwareEquivCandidate_congr firstIff secondIff

/-- **The model-assembled candidate is forward-closed under one `Step`** (member CR2), given the component
carriers' reducibility candidacy — per-tag dispatch (`pairLike` → the minimized projection CR2, the other two →
`dataTaitCandidate.closedUnderStep`).  Needs only `IsReducibilityCandidate` on each component (NOT full
`CarrierObligations`). -/
theorem CarrierCombinator.assembleModel_closedUnderStep {scope : Nat} (combinator : CarrierCombinator)
    (firstCandidate secondCandidate : RawTerm scope → Prop)
    (firstClosedUnderStep : ∀ {term reduct : RawTerm scope},
        firstCandidate term → Step term reduct → firstCandidate reduct)
    (secondClosedUnderStep : ∀ {term reduct : RawTerm scope},
        secondCandidate term → Step term reduct → secondCandidate reduct)
    {term reduct : RawTerm scope}
    (member : combinator.assembleModel firstCandidate secondCandidate term) (step : Step term reduct) :
    combinator.assembleModel firstCandidate secondCandidate reduct := by
  cases combinator
  · exact projectionPairCandidate_closedUnderStep firstClosedUnderStep secondClosedUnderStep member step
  · exact dataTaitCandidate.closedUnderStep member step
  · exact dataTaitCandidate.closedUnderStep member step

/-- **The model-assembled candidate is closed under member weak-head expansion**, given `CarrierObligations` —
per-tag dispatch (`pairLike` → projection weak-head expansion, the other two →
`dataTaitCandidate_memberWeakHeadExpansion`). -/
theorem CarrierCombinator.assembleModel_memberWeakHeadExpansion {scope : Nat} (combinator : CarrierCombinator)
    (firstCandidate secondCandidate : RawTerm scope → Prop)
    (firstWeakHeadExpansion : ∀ {source reduct : RawTerm scope},
        WeakHeadStep source reduct → IsStronglyNormalizing source → firstCandidate reduct →
        firstCandidate source)
    (secondWeakHeadExpansion : ∀ {source reduct : RawTerm scope},
        WeakHeadStep source reduct → IsStronglyNormalizing source → secondCandidate reduct →
        secondCandidate source)
    {source reduct : RawTerm scope}
    (weakHeadStep : WeakHeadStep source reduct) (sourceStronglyNormalizing : IsStronglyNormalizing source)
    (reductMember : combinator.assembleModel firstCandidate secondCandidate reduct) :
    combinator.assembleModel firstCandidate secondCandidate source := by
  cases combinator
  · exact projectionPairCandidate_memberWeakHeadExpansion firstWeakHeadExpansion secondWeakHeadExpansion
      weakHeadStep sourceStronglyNormalizing reductMember
  · exact dataTaitCandidate_memberWeakHeadExpansion weakHeadStep sourceStronglyNormalizing reductMember
  · exact dataTaitCandidate_memberWeakHeadExpansion weakHeadStep sourceStronglyNormalizing reductMember

end FX1Poly.Core
