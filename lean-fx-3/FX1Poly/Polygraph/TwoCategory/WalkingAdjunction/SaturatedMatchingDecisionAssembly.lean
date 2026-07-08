import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyOracleDispatch
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyCellDegenerate

/-! # SaturatedMatchingDecisionAssembly — the unconditional fib-3 saturated decision

This is the downstream ASSEMBLY that ties the whole matching-route chain together into a
single unconditional, zero-axiom inhabitant of the walking-adjunction saturated 2-cell
decision.  Every producer it composes is already shipped and audited; this file writes the
one glue term the chain was missing.

The chain, bottom to top:

  * **floor** — `cellValleyTraceEquiv_holds : CellValleyTraceEquiv`
    (`SpineValleyCellDegenerate`), UNCONDITIONAL (both Tier-D residuals closed).
  * **JOIN** — `matchingReductsShareSpineTrace_of_valleyTraceEquiv`
    (`SpineValleyOracleDispatch`) composes the CLOSED per-step oracle
    `valleyCellDescentStepOracle` into the reduction, so feeding the floor gives
    `MatchingReductsShareSpineTrace` with NO open hypothesis.
  * **keystone** — `saturatedMatchingCanonicalization_ofMatchingReductsShareSpineTrace`
    (`SaturatedSpineTraceLift`) builds the WHOLE `SaturatedMatchingCanonicalization`:
    SOUNDNESS from the shipped boundary-disciplined route
    (`saturatedMatchingCanonicalization_ofBoundaryDiscipline` on
    `matchingSaturatedCongruence_proved`), COMPLETENESS from the JOIN.
  * **decision** — `decideSaturatedConvViaMatching` / `adjunctionSaturatedWordProblemModuloMatching`
    (`SaturatedMatchingCanonicalization`) turns the canonicalization into a structural
    `Decidable` on the boundary `matchingOf` (`DiagramType` `DecidableEq`, no `propext`).

Result: `SaturatedMatchingCanonicalization` is INHABITED unconditionally, and saturated
2-cell convertibility of the walking adjunction is DECIDABLE, both zero-axiom.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The JOIN, unconditional -/

/-- ★ **`MatchingReductsShareSpineTrace` holds UNCONDITIONALLY.**  Feed the unconditional
Track-B floor `cellValleyTraceEquiv_holds` into the sharpened reduction
`matchingReductsShareSpineTrace_of_valleyTraceEquiv` — whose oracle premise is already
discharged internally by the closed dispatch `valleyCellDescentStepOracle`.  No open
hypothesis remains. -/
theorem matchingReductsShareSpineTrace_holds : MatchingReductsShareSpineTrace :=
  matchingReductsShareSpineTrace_of_valleyTraceEquiv cellValleyTraceEquiv_holds

/-! ## The keystone, inhabited -/

/-- ★ **The `SaturatedMatchingCanonicalization` is INHABITED, unconditionally.**  Apply the
keystone `saturatedMatchingCanonicalization_ofMatchingReductsShareSpineTrace` to the
unconditional JOIN: SOUNDNESS is consumed from the shipped boundary-disciplined route,
COMPLETENESS from the JOIN.  This is the term the ledger's `hasSaturatedCompleteness` and
the marker `fxMode_hasSaturatedMatchingCanonicalization` are now backed by. -/
def saturatedMatchingCanonicalization_holds : SaturatedMatchingCanonicalization :=
  saturatedMatchingCanonicalization_ofMatchingReductsShareSpineTrace
    matchingReductsShareSpineTrace_holds

/-! ## The decision, unconditional -/

/-- ★ **Saturated 2-cell convertibility of the walking adjunction is DECIDABLE,
unconditionally.**  Supply the inhabited canonicalization to
`adjunctionSaturatedWordProblemModuloMatching`: every parallel pair of free 2-cells is
decided by comparing boundary matchings with the structural `DiagramType` `DecidableEq`
(no `propext`, no fuel).  The term the ledger's `hasSaturatedDecision` is backed by. -/
@[reducible] def decideSaturatedTwoCellConv_ofSeed : DecidableSaturatedTwoCellConvFor :=
  adjunctionSaturatedWordProblemModuloMatching saturatedMatchingCanonicalization_holds

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the fib-3 saturated matching decision is ASSEMBLED, unconditional and
zero-axiom.**  `saturatedMatchingCanonicalization_holds` inhabits the keystone with no open
hypothesis, and `decideSaturatedTwoCellConv_ofSeed` decides saturated convertibility for
every parallel pair.  Backs the ledger rung-2 completeness and decision fields.  `= true`. -/
def fxMode_hasSaturatedMatchingDecisionAssembled : Bool := true

end FX1Poly.Polygraph
