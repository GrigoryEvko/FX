import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutRightImageDecision
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutShiftedGapSplice

/-! # Polygraph/TwoCategory/Amalgam/PushoutReseatFillWiring — wiring the per-gap TWO-SIDED DECISION into a
splice-ready wall/gap fill (WP-AMALG-2 r7, B1)

`PushoutWireChangeLedger.lean`'s node (ii) — the per-gap gap-EZ reseat assembly `wordMul_vcompGen ∘ reseatReflect`
— is already DISCHARGED as a two-sided decision: `pushoutRightImageTwoSidedDecision` (`PushoutRightImageDecision.lean`)
decides pushout convertibility of ANY pair of right-coprojected reconstructed cells (wire-changing included).  What
r6 left as "trivial wiring" is the last hop: turn a per-gap DECISION verdict into a `ShiftedGapFill` that the
wire-changing splice `multiGapShiftedSplice` (`PushoutShiftedGapSplice.lean`) threads into wall-position.  This file
ships that wiring — with the truth-probe on a concrete per-gap fill FIRST.

## The truth-probe FIRST, then the wiring

The concrete per-gap fill is truth-probed BEFORE the wiring is built: `pushoutRightImageDecidesTwoSided_assoc`
(re-`#eval`ed here) already certifies the two-sided decider returns `isTrue` on the associativity gap
(`reconAssocLeftCell` / `reconAssocRightCell`, `t³ ⇒ t`), and `false` on the separating faces.  Only THEN does the
wiring lift the `isTrue` verdict into a fill.

## What ships (each zero-axiom, STRUCTURAL, ASCII-only)

  * **`reseatGapFillOfConv`** — the GENERAL wiring: any pushout right-image convertibility of two reconstructed
    cells packs into a `ShiftedGapFill` at the pushout's single mode.  Generalises the two hard-coded r6 fills
    (`shiftedAssocGapFill` / `shiftedLeftUnitGapFill`) to an arbitrary decided/proved right-image conv.
  * **`reseatDecisionDrivenAssocFill` / `reseatDecisionDrivenLeftUnitFill`** — the fills built by EXTRACTING the
    conv from the two-sided DECISION's `isTrue` verdict (not a hard-coded conv): the decision genuinely drives the
    fill.  The `isFalse` branch is refuted by the shipped base-case conv (`pushoutAssocGapConv` /
    `pushoutLeftUnitGapConv`).
  * **`reseatDecisionDrivenSpliceWitness`** — the two decision-driven fills threaded END-TO-END through
    `multiGapShiftedSplice` on the two-`s`-wall layout: per-gap decision ⟹ splice-ready fill ⟹ one boundary
    convertibility.  The full B1 chain, decision-driven.

This is the reseat ASSEMBLY (node (ii)) closed at the granularity of the shipped per-gap decision + the shipped
wire-changing splice.  The remaining residual is node (i) — the whole-cell factorization that PRODUCES the per-gap
list from an arbitrary cell (the top induction, `PushoutVcompInterchangeSplice.lean`'s crux + the reconstruction
bridge).  `fxAmalg_hasFullSaturatedPushoutDispatch` STAYS `false`; #2043 does NOT close.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The truth-probe FIRST — the concrete per-gap fill decides true -/

-- Truth-probe (FIRST): the two-sided decider returns `true` on the associativity gap's right-images. Expect `true`.
#eval pushoutRightImageDecidesTwoSided reconAssocLeftCell reconAssocRightCell
-- ... and `false` on the separating faces (the decision is genuinely two-sided). Expect `false`.
#eval pushoutRightImageDecidesTwoSided reconFaceDeltaOne reconFaceDeltaZero

/-! ## The general wiring: right-image conv ⟹ splice-ready wall/gap fill -/

/-- ★ **The reseat wiring — a pushout right-image convertibility packs into a splice-ready wall/gap fill.**  Given
two reconstructed monad cells `cellA` / `cellB` (parallel single-gap words) and a pushout convertibility of their
right-coprojection images over the real-law relation, produces a `ShiftedGapFill` at the pushout's single mode
`monadPushMode`: the images become the fill's `source` / `target`, the conv its `fill`.  Generalises the two r6
hard-coded fills to an ARBITRARY decided/proved right-image conv — the per-gap output of
`pushoutRightImageTwoSidedDecision` becomes a splice input. -/
def reseatGapFillOfConv
    {sourcePath targetPath : ModalityPath monadComputad.toModeGraph
      (⟨0, by decide⟩ : Fin monadComputad.modeCount) (⟨0, by decide⟩ : Fin monadComputad.modeCount)}
    {cellA cellB : RawTwoCellExpr monadComputad.toModeSignature sourcePath targetPath}
    (conv : SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel
      (mapCellAlong (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes) cellA)
      (mapCellAlong (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes) cellB)) :
    ShiftedGapFill involutionMonadPushout.toModeSignature crossPairRealPushoutRel monadPushMode :=
  ⟨_, _,
    mapCellAlong (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes) cellA,
    mapCellAlong (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes) cellB,
    conv⟩

/-! ## The decision-driven fills — the DECISION verdict builds the fill -/

/-- ★★ **The associativity gap fill, DECISION-DRIVEN.**  The `ShiftedGapFill` for the `mu`-associativity gap built
by EXTRACTING the convertibility from the two-sided decider's `isTrue` verdict — the decision genuinely drives the
fill (not a hard-coded conv).  The `isFalse` branch is impossible: the shipped base-case `pushoutAssocGapConv`
inhabits exactly the conv the verdict would deny. -/
def reseatDecisionDrivenAssocFill :
    ShiftedGapFill involutionMonadPushout.toModeSignature crossPairRealPushoutRel monadPushMode :=
  match pushoutRightImageTwoSidedDecision reconAssocLeftCell reconAssocRightCell with
  | isTrue conv => reseatGapFillOfConv conv
  | isFalse hn => absurd pushoutAssocGapConv hn

/-- ★★ **The left-unit gap fill, DECISION-DRIVEN.**  The `ShiftedGapFill` for the `eta` left-unit gap built by
extracting the conv from the two-sided decider's `isTrue` verdict; the `isFalse` branch refuted by the shipped
`pushoutLeftUnitGapConv`. -/
def reseatDecisionDrivenLeftUnitFill :
    ShiftedGapFill involutionMonadPushout.toModeSignature crossPairRealPushoutRel monadPushMode :=
  match pushoutRightImageTwoSidedDecision reconLeftUnitCell reconIdTCell with
  | isTrue conv => reseatGapFillOfConv conv
  | isFalse hn => absurd pushoutLeftUnitGapConv hn

/-! ## The decision-driven end-to-end splice -/

/-- ★★★ **The full B1 chain, DECISION-DRIVEN.**  The two decision-driven fills threaded end-to-end through the
wire-changing splice `multiGapShiftedSplice` on the two-`s`-wall layout `[assoc (t³ ⇒ t), leftUnit (t ⇒ t)]`: each
gap's fill came from the two-sided DECISION's `isTrue` verdict, and the splice normalizes the presented layout to
its all-gaps-normalized form across both `s`-walls.  This is the reseat assembly (node (ii)) closed at the shipped
granularity: per-gap decision ⟹ splice-ready fill ⟹ one boundary convertibility. -/
def reseatDecisionDrivenSpliceWitness :
    SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel
      (shiftedGapSourceCell monadPushSPath [reseatDecisionDrivenAssocFill, reseatDecisionDrivenLeftUnitFill])
      (shiftedGapTargetCell monadPushSPath [reseatDecisionDrivenAssocFill, reseatDecisionDrivenLeftUnitFill]) :=
  multiGapShiftedSplice monadPushSPath [reseatDecisionDrivenAssocFill, reseatDecisionDrivenLeftUnitFill]

/-! ## Honesty marker -/

/-- ★★ **Honesty marker — the per-gap DECISION-to-FILL reseat wiring SHIPS (WP-AMALG-2 r7, B1).**  `= true`:
`reseatGapFillOfConv` lifts an arbitrary pushout right-image convertibility into a splice-ready `ShiftedGapFill`
(generalising the two r6 hard-coded fills), and `reseatDecisionDrivenAssocFill` / `reseatDecisionDrivenLeftUnitFill`
build the fills by EXTRACTING the conv from the shipped two-sided decider `pushoutRightImageTwoSidedDecision`'s
`isTrue` verdict (truth-probed FIRST: `pushoutRightImageDecidesTwoSided_assoc`).  `reseatDecisionDrivenSpliceWitness`
threads both decision-driven fills END-TO-END through `multiGapShiftedSplice` across two `s`-walls — the reseat
assembly (`PushoutWireChangeLedger.lean` node (ii)) closed at the shipped per-gap-decision + wire-changing-splice
granularity.  The remaining residual is node (i): the top induction that PRODUCES the per-gap list from an arbitrary
cell (the crux `vcompGapInterchangeSplice` + the reconstruction bridge).
`fxAmalg_hasFullSaturatedPushoutDispatch` (`DispatchSaturated.lean`) STAYS `false`; #2043 does NOT close.  `= true`. -/
def fxAmalg_hasReseatFillWiring : Bool := true

end FX1Poly.Polygraph.Amalgam
