import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingStaircaseReduction
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineTraceReconstruction

/-! # mode-3 keystone — the free-trace lift into the saturated relation + the existence-factored reduction

The `matchingOf`-carrier completeness field `convOfMapEq` (`matchingOf cellA = matchingOf cellB →
SaturatedTwoCellConv cellA cellB`) is the sole remaining residual for both fib-3 gate flips (soundness
is CLOSED, `SaturatedMatchingStaircaseReduction`).  Two shipped facts sit at the boundary between the
FREE decision layer and the SATURATED relation:

  * `RawTwoCellExpr.twoCellConvFull_ofSpineTraceEquiv` (FREE-4, `SpineTraceReconstruction`): spines that
    are trace-equivalent realize as a `TwoCellConvFull` between the cells — the free Mazurkiewicz word
    problem, decided;
  * `SaturatedTwoCellConv.ofFull` (`SaturatedDecision`): every completed free convertibility embeds into
    the saturated relation.

This file composes them into the **currency-converter** the completeness route needs, then uses it to
ship an EXISTENCE-factored keystone reduction:

  * ★ `SaturatedTwoCellConv.ofSpineTraceEquiv` — trace-equivalent spines lift straight to
    `SaturatedTwoCellConv` (unconditionally; the companion of `SaturatedTwoCellConv.ofConv`).  This is
    exactly the shape that consumes `fxMode_hasArcCellReconstruction` (#1996,
    `arcStructureOf a = arcStructureOf b → SpineTraceEquiv a.spine b.spine`) — the campaign's active node
    outputs `SpineTraceEquiv`, and this converts it to the keystone's currency;
  * `MatchingReductsShareSpineTrace` — the completeness residual re-factored by EXISTENCE (not by a
    canonical-cell function as in `CanonicalMatchingStaircaseData`): matching-equal cells have saturated
    reducts whose spines are trace-equivalent.  Because `arcStructureOf` is STRICTLY finer than
    `matchingOf` (it separates the snake from the identity — `SpineTraceDecision`), the coarser
    `matchingOf` hypothesis cannot feed #1996 directly; the reducts are where the triangle
    (snake-straightening) removes the finer/coarser gap so the residual `SpineTraceEquiv` conjunct is
    exactly #1996's output on the reducts;
  * ★ `convOfMapEq_ofMatchingReductsShareSpineTrace` — the reduction: the existence residual yields
    `convOfMapEq`, glued `cellA ≈ reductA ≈[lift] reductB ≈ cellB` by saturated trans/symm;
  * ★ `saturatedMatchingCanonicalization_ofMatchingReductsShareSpineTrace` — the WHOLE keystone from the
    existence residual alone (soundness consumed from the boundary discipline, completeness from the
    reduction) — a second, existence-only route to the keystone alongside the canonical-staircase one.

Raw Lean 4 + Init; the lift is `ofFull ∘ twoCellConvFull_ofSpineTraceEquiv`, the reduction is saturated
trans/symm glue; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The free-trace lift into the saturated relation.**  Trace-equivalent spines lift to
`SaturatedTwoCellConv`: run the shipped free reconstruction `twoCellConvFull_ofSpineTraceEquiv` (spines
trace-equivalent ⟹ `TwoCellConvFull`), then embed via `SaturatedTwoCellConv.ofFull`.  The companion of
`SaturatedTwoCellConv.ofConv` for the trace layer, and exactly the currency-converter that turns the
`SpineTraceEquiv` output of the arc cell reconstruction (#1996) into the keystone's `SaturatedTwoCellConv`
currency.  Unconditional. -/
theorem SaturatedTwoCellConv.ofSpineTraceEquiv {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (cellFirst cellSecond : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath)
    (traceEquiv : SpineTraceEquiv adjunctionModeSignature cellFirst.spine cellSecond.spine) :
    SaturatedTwoCellConv cellFirst cellSecond :=
  SaturatedTwoCellConv.ofFull
    (RawTwoCellExpr.twoCellConvFull_ofSpineTraceEquiv cellFirst cellSecond traceEquiv)

/-- The **completeness residual, existence-factored**: every pair of cells with equal boundary matchings
has a pair of saturated REDUCTS (each saturated-convertible to its source cell) whose spines are
trace-equivalent.  The existence-based sibling of `MatchingStaircaseReconstructs` (which fixes a canonical
cell FUNCTION): here nothing canonical is chosen — only the existence of trace-equivalent-spined reducts
is asserted.  The `SpineTraceEquiv` conjunct is precisely the output of the arc cell reconstruction
(#1996) applied to the reducts, so once #1996 lands this residual is exactly the SNAKE-STRAIGHTENING to
arc-taut reducts (removing the finer/coarser gap between `arcStructureOf` and `matchingOf`). -/
def MatchingReductsShareSpineTrace : Prop :=
  ∀ {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath),
    matchingOf cellA = matchingOf cellB →
    ∃ reductA reductB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath,
      SaturatedTwoCellConv cellA reductA ∧ SaturatedTwoCellConv cellB reductB ∧
        SpineTraceEquiv adjunctionModeSignature reductA.spine reductB.spine

/-- ★ **The completeness reduction from the existence residual.**  `MatchingReductsShareSpineTrace`
yields the keystone's completeness direction `convOfMapEq`: the reducts' trace-equivalent spines lift to
`SaturatedTwoCellConv` (`ofSpineTraceEquiv`), and the glue `cellA ≈ reductA ≈ reductB ≈ cellB` closes by
saturated transitivity and symmetry.  A route to `convOfMapEq` that does NOT require choosing a canonical
cell — only the existence of trace-equivalent-spined saturated reducts. -/
theorem convOfMapEq_ofMatchingReductsShareSpineTrace
    (shares : MatchingReductsShareSpineTrace)
    {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath)
    (matchingsEqual : matchingOf cellA = matchingOf cellB) :
    SaturatedTwoCellConv cellA cellB := by
  obtain ⟨reductA, reductB, convReductA, convReductB, traceEquiv⟩ :=
    shares cellA cellB matchingsEqual
  exact SaturatedTwoCellConv.trans convReductA
    (SaturatedTwoCellConv.trans
      (SaturatedTwoCellConv.ofSpineTraceEquiv reductA reductB traceEquiv)
      (SaturatedTwoCellConv.symm convReductB))

/-- ★ **The whole keystone from the existence residual alone.**  A `MatchingReductsShareSpineTrace`
determines a complete `SaturatedMatchingCanonicalization`: the SOUNDNESS field is consumed from the
shipped boundary-disciplined route (`saturatedMatchingCanonicalization_ofBoundaryDiscipline` on the
shipped `matchingSaturatedCongruence_proved`), the COMPLETENESS field from the reduction above.  A second,
existence-only route to the entire fib-3 keystone alongside
`saturatedMatchingCanonicalization_ofMatchingStaircase`. -/
def saturatedMatchingCanonicalization_ofMatchingReductsShareSpineTrace
    (shares : MatchingReductsShareSpineTrace) : SaturatedMatchingCanonicalization :=
  saturatedMatchingCanonicalization_ofBoundaryDiscipline matchingSaturatedCongruence_proved
    (fun matchingsEqual => convOfMapEq_ofMatchingReductsShareSpineTrace shares _ _ matchingsEqual)

/-! ## Honesty marker -/

/-- **Honesty marker — the free-trace lift into the saturated relation is PROVED, unconditional.**
`SaturatedTwoCellConv.ofSpineTraceEquiv` lifts any `SpineTraceEquiv` of spines to `SaturatedTwoCellConv`
by composing the shipped free reconstruction with the `ofFull` embedding — the currency-converter that
turns the arc cell reconstruction's (#1996) `SpineTraceEquiv` output into the keystone's currency.  What
this marker does NOT claim: `MatchingReductsShareSpineTrace` (the existence residual — the reducts with
trace-equivalent spines whose existence is the snake-straightening still owed), nor therefore an
inhabitant of the keystone `SaturatedMatchingCanonicalization`.  What it DOES establish: the reduction
`convOfMapEq_ofMatchingReductsShareSpineTrace` and the capstone
`saturatedMatchingCanonicalization_ofMatchingReductsShareSpineTrace` — so the whole keystone follows from
that one existence residual, a route needing no canonical-cell choice.  `= true`. -/
def fxMode_hasSpineTraceLiftIntoSaturated : Bool := true

end FX1Poly.Polygraph
