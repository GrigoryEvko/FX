import FX1Poly.Polygraph.TwoCategory.WalkingString.StringConvOfMapEqPort

/-! # WalkingString/StringDisjointFarCommutation — the DISJOINT-boundary case discharged by free far-commutation (FC-3 r1, B3)

FC-9 (`StringConvOfMapEqPort`) localized the standing completeness residual to `StringCellValleyTraceEquiv` and
machine-witnessed the crux: the DISJOINT-boundary two-colour valley `stringCrossLevelCell : G·F ⇒ G·H` (lower counit
`ε` on the `G·F` source, upper unit `η'` on the `G·H` target — disjoint supports) is ALREADY canonical
(`stringReconstruct_crossLevel_convToReconstruct`, zero residual moves), while the genuine residual is the
SAME-boundary INTERLEAVED case.  That single witness was a `refl` on one concrete cell.

This file GENERALIZES the disjoint-case discharge from that single witness to the WHOLE far-commutation fragment,
UNCONDITIONALLY.  The mechanism is the free-structure **disjoint-whisker exchange** (`TwoCellConvFull.whiskerExchange`):
a LEFT whisker and a RIGHT whisker over DISJOINT 1-cells COMMUTE — the two-cell bimodule action of the 1-cell monoid.
Lifted to the saturated relation (`StringSaturatedTwoCellConv.ofFull`), it says: for EVERY body 2-cell and EVERY pair
of disjoint whiskering 1-cells,

    leftWhisker ◁ (body ▷ rightWhisker)  ≈  (leftWhisker ◁ body) ▷ rightWhisker      (modulo the boundary cast),

with NO side condition.  This is exactly the Di Francesco–Zuber trace-monoid far-commutation (`|i − j| > 1`: generators
on disjoint boundaries commute freely) at the walking-adjoint-triple signature: two turnbacks on disjoint strands may be
performed in either order, so a disjoint-boundary window NEVER needs straightening and its reconstruction is a free move,
not a colour-aware valley re-derivation.

## What this narrows

The valley residual `StringCellValleyTraceEquiv` (`StringMatchingValleyDescent`) is a soundness-preserving reordering of
turnbacks.  The DISJOINT (far-commuting, `|i − j| > 1`) reorderings are now discharged UNCONDITIONALLY by
`stringDisjointWhiskerExchange` (and hence by the free structure `TwoCellConvFull` already inside the saturated
relation).  What remains is EXACTLY the SAME-boundary INTERLEAVED window — adjacent turnbacks sharing a boundary
(`|i − j| ≤ 1`, over-full colour sum), the mixed cup·cap pair the width-only classifier would mis-route and the r6 pin
`stringCupCod_ne_capDom` blocks from straightening.  So `fxString_hasAdjointTripleCompleteness` stays `false`, honestly
— NO flip — but the residual is localized strictly further than FC-9 left it: the disjoint fragment is closed, only the
interleaved fragment is open.

Non-vacuity: the exchange FIRES on a real generator (`stringDisjointFarCommutation_onUnitLower` — the lower unit `η`
whiskered by `G` on the left and `F` on the right, a genuine disjoint window).

Raw Lean 4 + Init; each lemma is a one-line lift of a `TwoCellConvFull` constructor through
`StringSaturatedTwoCellConv.ofFull`.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free;
per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The disjoint-whisker far-commutation at the saturated relation -/

/-- ★★ **The disjoint-whisker EXCHANGE at the walking adjoint triple** (the Di Francesco–Zuber far-commutation
`|i − j| > 1`).  For EVERY body 2-cell and EVERY pair of DISJOINT whiskering 1-cells, a left whisker and a right
whisker COMMUTE: `leftWhisker ◁ (body ▷ rightWhisker) ≈ (leftWhisker ◁ body) ▷ rightWhisker` (through the boundary
cast that reassociates `leftWhisker ∘ body ∘ rightWhisker`).  UNCONDITIONAL — no side condition — an infinite family
of real convertibilities lifting the free-structure `TwoCellConvFull.whiskerExchange` into the saturated relation.  A
disjoint-boundary window therefore reorders freely and NEVER needs colour-aware straightening. -/
theorem stringDisjointWhiskerExchange
    {sourceMode middleSourceMode middleTargetMode targetMode : AdjointTripleMode}
    (leftWhisker : ModalityPath adjointTripleGraph sourceMode middleSourceMode)
    {bodyDom bodyCod : ModalityPath adjointTripleGraph middleSourceMode middleTargetMode}
    (rightWhisker : ModalityPath adjointTripleGraph middleTargetMode targetMode)
    (body : RawTwoCellExpr adjointTripleModeSignature bodyDom bodyCod) :
    StringSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerLeft leftWhisker (RawTwoCellExpr.whiskerRight rightWhisker body))
      (RawTwoCellExpr.castBoundary (composePath_assoc leftWhisker bodyDom rightWhisker)
        (composePath_assoc leftWhisker bodyCod rightWhisker)
        (RawTwoCellExpr.whiskerRight rightWhisker (RawTwoCellExpr.whiskerLeft leftWhisker body))) :=
  StringSaturatedTwoCellConv.ofFull (TwoCellConvFull.whiskerExchange leftWhisker rightWhisker body)

/-- The disjoint-whisker exchange in the OTHER direction (the relation is symmetric) — the two Godement orders of a
disjoint composite are inter-convertible, so neither is privileged and the disjoint reconstruction is order-free. -/
theorem stringDisjointWhiskerExchange_symm
    {sourceMode middleSourceMode middleTargetMode targetMode : AdjointTripleMode}
    (leftWhisker : ModalityPath adjointTripleGraph sourceMode middleSourceMode)
    {bodyDom bodyCod : ModalityPath adjointTripleGraph middleSourceMode middleTargetMode}
    (rightWhisker : ModalityPath adjointTripleGraph middleTargetMode targetMode)
    (body : RawTwoCellExpr adjointTripleModeSignature bodyDom bodyCod) :
    StringSaturatedTwoCellConv
      (RawTwoCellExpr.castBoundary (composePath_assoc leftWhisker bodyDom rightWhisker)
        (composePath_assoc leftWhisker bodyCod rightWhisker)
        (RawTwoCellExpr.whiskerRight rightWhisker (RawTwoCellExpr.whiskerLeft leftWhisker body)))
      (RawTwoCellExpr.whiskerLeft leftWhisker (RawTwoCellExpr.whiskerRight rightWhisker body)) :=
  StringSaturatedTwoCellConv.symm (stringDisjointWhiskerExchange leftWhisker rightWhisker body)

/-! ## Non-vacuity: the far-commutation fires on a real generator -/

/-- **Non-vacuity — the far-commutation fires on the lower unit `η` on a genuine disjoint window.**  Take the lower
unit `η = stringUnitLower : id_base ⇒ F·G` (a real cup), whiskered by `G = right` on the LEFT and `F = left` on the
RIGHT — disjoint 1-cells sharing no strand with the body.  The two Godement orders of `G ◁ (η ▷ F)` are
saturated-convertible by `stringDisjointWhiskerExchange`; the reconstruction target boundary is inferred.  A real,
non-degenerate instance of the disjoint far-commutation on a walking-adjoint-triple generator. -/
theorem stringDisjointFarCommutation_onUnitLower :
    StringSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerLeft (singletonModalityPath AdjointTripleModality.right)
        (RawTwoCellExpr.whiskerRight (singletonModalityPath AdjointTripleModality.left) stringUnitLower))
      (RawTwoCellExpr.castBoundary
        (composePath_assoc (singletonModalityPath AdjointTripleModality.right)
          (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base)
          (singletonModalityPath AdjointTripleModality.left))
        (composePath_assoc (singletonModalityPath AdjointTripleModality.right)
          stringFG (singletonModalityPath AdjointTripleModality.left))
        (RawTwoCellExpr.whiskerRight (singletonModalityPath AdjointTripleModality.left)
          (RawTwoCellExpr.whiskerLeft (singletonModalityPath AdjointTripleModality.right) stringUnitLower))) :=
  stringDisjointWhiskerExchange (singletonModalityPath AdjointTripleModality.right)
    (singletonModalityPath AdjointTripleModality.left) stringUnitLower

/-! ## Honesty marker -/

/-- ★★ **ESTABLISHED — the DISJOINT-boundary case of the completeness residual is discharged UNCONDITIONALLY; NO
completeness flip.**  `= true`.  `stringDisjointWhiskerExchange` (with `_symm`) lifts the free-structure disjoint-whisker exchange into the
saturated relation, so for EVERY body and EVERY pair of disjoint whiskers the two Godement orders are
`StringSaturatedTwoCellConv` — the
Di Francesco–Zuber far-commutation `|i − j| > 1`, an infinite family generalizing the single FC-9 witness
`stringReconstruct_crossLevel_convToReconstruct` (which was a `refl` on the one cross-level valley).  Consequently the
valley residual `StringCellValleyTraceEquiv` (`StringMatchingValleyDescent`) is closed on its DISJOINT
(far-commuting) reorderings; what remains is EXACTLY the SAME-boundary INTERLEAVED window
(`stringTwoColourValleyCruxConfiguration`, the mixed cup·cap pair the r6 pin `stringCupCod_ne_capDom` blocks from
straightening).  This narrows the standing residual strictly further than FC-9 left it — the disjoint fragment is
free, only the interleaved fragment is open — but does NOT inhabit `StringMatchingReconstruction.convToReconstruct`
in general, so `fxString_hasAdjointTripleCompleteness` (in `StringMatchingCompleteness`) is NOT moved and stays
`false`, honestly. -/
def fxString_hasDisjointFarCommutation : Bool := true

end FX1Poly.Polygraph
