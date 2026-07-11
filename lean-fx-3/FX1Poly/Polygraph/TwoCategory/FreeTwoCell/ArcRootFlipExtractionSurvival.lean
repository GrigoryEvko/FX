import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCoreSwapCapFlipRefutation

/-! # MODE-COMMUTE — the arc EXTRACTION SURVIVES the counit/cap root flip (the non-vacuity terminal)

`ArcCoreSwapCapFlipRefutation` (r4) machine-refuted the ROOT-level count vehicle
`ArcGodementCoreSwapSimCount` at the counit/cap join-order flip: the merged component roots at `6`
under the redex order and `5` under the reduct order while wires `5, 6` both survive open, so
`ArcStepSimCount.rootComm` forces `5 = 6` (`not_arcGodementCoreSwapSimCount_adjunction`).  r4's
positive control (`arcRootFlip_partitionAgrees`) then SAMPLED three partition-view quantities — the
loops, one survivor-port same-component boolean, one per-port cap count — and found them to agree,
concluding the surgery target survives.

This file DELIVERS the terminal fact r4 stopped short of: at the very flip that kills the root
vehicle, the FULL partition view agrees (`SameArcPartition`, every in-range boundary index and every
port, not three samples) and hence the OBSERVABLE the compiler reads — the `extractArc`
`FullArcStructure` — is LITERALLY EQUAL across the two run orders.  This is the non-vacuity gate for
the whole component-surgery program at its sharpest witness: the component route does not merely
replace a dead vehicle with a differently-stated one, it DELIVERS equal extraction exactly where the
root-count vehicle is machine-refuted.

## The route (why this is kernel-cheap and zero-axiom)

A brute `decide`/`rfl` on `extractArc … redex = extractArc … reduct` TIMES OUT (its `diagram :=
extractDiagram …` field runs the full matching canonicalization — a large kernel computation).  The
survival is instead obtained the RIGHT way, via the shipped factoring THEOREM
`extractArc_eq_of_sameArcPartition`: build `SameArcPartition` — whose fields are the CHEAP
partition-determined quantities (`boundarySameComponent`, `internalEventCountAt`), never touching
`extractDiagram` — then lift to extraction equality abstractly.  The nested double-index conjunct is
discharged through a reassociated bounded-`∀` helper (`∀ i, i < n → ∀ j, j < n → …`, two nested
`Nat.decidableBallLT`) that `decide` CAN synthesize, unlike the raw
`∀ i j, i < n → j < n → …` shape `SameArcPartition` states.

The two run orders' surviving open wires are `[5, 6]`, so at `bottomCount = 0` the boundary nodes ARE
`[5, 6]` (r4's positive-control base); a `bottomCount = 2` variant confirms the invariance is robust
to reading additional (isolated) bottom ports.

## What this file does NOT claim

  * It does NOT flip any standing obligation.  `fxMode_hasArcGodementSwapRenameableProof` (the general
    renaming witness) and `fxMode_hasArcPeelGeneralSignature` (the general-signature peel, r6) stay
    `false`; `fxMode_hasArcCoreSwapSimCountRefuted` stays `true` — this certificate is CONSISTENT with
    the refutation (root vehicle dead, extraction alive), not a re-opening of it.
  * It certifies the decidable READOUT (`SameArcPartition`) plus the observable (`extractArc`) at ONE
    concrete witness — NOT the unbounded component-simulation structure `ArcPartitionSim` (whose
    `componentsCorr` quantifies over all of `Nat`), and NOT the general empty-boundary closure
    (`fxMode_hasArcGodementSoundnessPeelEmptyBoundary` stays `false`).

Raw Lean 4 + Init; the flip cores are tiny (6 wires, 3 forest edges, 2 caps), so every `decide` is
kernel-cheap — the obstruction-smoke idiom, NOT a large-cell decide (`extractArc` itself is never
decided).  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The counit/cap root-flip cores (the r4 witness, re-exposed for the survival readout)

Re-declared here because r4's `arcRootFlipRedexCore` / `arcRootFlipReductCore` are `private`.  These
are the SAME two Godement run orders from the same fresh forest state `openWires = [1..6]`,
`links = [(1,3),(2,5),(4,6)]`, `nextFresh = 7`: two `counit` caps applied in the two window orders. -/

/-- The root-flip state: six open wires, three forest edges, `nextFresh = 7`, no prior events. -/
private def arcFlipState : ArcWireState :=
  { openWires := [1, 2, 3, 4, 5, 6], links := [(1, 3), (2, 5), (4, 6)], nextFresh := 7, loops := 0,
    cupEventNodes := [], capEventNodes := [] }

/-- The identity 2-cell on `right·left`, the common `cellAlpha` prefix of both run orders. -/
private def arcFlipIdentityCell :
    RawTwoCellExpr adjunctionModeSignature adjunctionRightThenLeft adjunctionRightThenLeft :=
  RawTwoCellExpr.id _

/-- The redex run order: `counit` cap at the f-window, then `counit` cap at the g-window offset `0`. -/
private def arcFlipRedexCore : ArcWireState :=
  runArcCell (runArcCell
      (runArcCell arcFlipState
        (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
        (composePath adjunctionRightThenLeft
          (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip))
        arcFlipIdentityCell)
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
      (composePath adjunctionRightThenLeft (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip))
      adjunctionCounitTwoCell)
    (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip))
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
    adjunctionCounitTwoCell

/-- The reduct run order: `counit` cap at the g-window offset `|right·left| = 2` FIRST, then f-window. -/
private def arcFlipReductCore : ArcWireState :=
  runArcCell (runArcCell
      (runArcCell arcFlipState
        (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
        (composePath adjunctionRightThenLeft
          (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip))
        arcFlipIdentityCell)
      (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip) adjunctionRightThenLeft)
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip) adjunctionCounitTwoCell)
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
    (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip))
    adjunctionCounitTwoCell

/-- ★ **The root vehicle is dead at this flip** — the merged component roots DIVERGE (`6` vs `5`) on
the surviving old wire `5`, exactly what `ArcStepSimCount.rootComm` cannot reconcile (r4's
`not_arcGodementCoreSwapSimCount_adjunction`).  Restated on these cores so the file is self-contained
about WHY the root-count vehicle fails here. -/
theorem arcFlip_rootsDiverge :
    unionFindRootOf arcFlipRedexCore.links 5 = 6 ∧ unionFindRootOf arcFlipReductCore.links 5 = 5 :=
  ⟨by decide, by decide⟩

/-! ## The full partition view agrees — and hence the extraction survives (bottomCount 0)

At `bottomCount = 0` the boundary nodes are the surviving open wires `[5, 6]` — the base of r4's
positive control, here strengthened from three samples to the COMPLETE `SameArcPartition`. -/

/-- The double-index boundary-same-component conjunct of `SameArcPartition`, in the reassociated
`∀ i, i < n → ∀ j, j < n → …` shape `decide` synthesizes (nested `Nat.decidableBallLT`).  Feeds the
raw `∀ i j, i < n → j < n → …` conjunct by supplying the arguments in order. -/
private theorem arcFlip_boundaryRelReassoc0 :
    ∀ firstIndex, firstIndex < 0 + arcFlipRedexCore.openWires.length →
      ∀ secondIndex, secondIndex < 0 + arcFlipRedexCore.openWires.length →
        boundarySameComponent 0 arcFlipRedexCore firstIndex secondIndex
          = boundarySameComponent 0 arcFlipReductCore firstIndex secondIndex := by
  decide

/-- ★ **The FULL partition view agrees across the flip (bottomCount 0).**  Every field of
`SameArcPartition` — open-wire count, loop count, the same-component relation on EVERY in-range
boundary index pair, and EVERY per-port internal cup/cap count — coincides between the two run orders.
This is r4's three-sample positive control promoted to the whole partition datum. -/
theorem arcFlip_samePartition0 : SameArcPartition 0 arcFlipRedexCore arcFlipReductCore :=
  ⟨by decide, by decide,
    fun firstIndex secondIndex firstInRange secondInRange =>
      arcFlip_boundaryRelReassoc0 firstIndex firstInRange secondIndex secondInRange,
    by decide, by decide⟩

/-- ★ **The arc EXTRACTION survives the root flip (bottomCount 0).**  The observable `FullArcStructure`
the compiler reads via `extractArc` is LITERALLY EQUAL across the two Godement run orders — obtained
from `arcFlip_samePartition0` through the factoring theorem `extractArc_eq_of_sameArcPartition` (the
cup/cap event-node length agreements are `[] = []` and `[8,7] = [8,7]`), NOT by deciding `extractArc`
itself.  The terminal non-vacuity fact: the component route delivers equal extraction exactly where
`ArcStepSimCount` is machine-refuted. -/
theorem arcFlip_extractsEqual0 :
    extractArc 0 arcFlipRedexCore = extractArc 0 arcFlipReductCore :=
  extractArc_eq_of_sameArcPartition 0 arcFlipRedexCore arcFlipReductCore
    arcFlip_samePartition0 (by decide) (by decide)

/-! ## Robustness — the extraction survives at a wider boundary read (bottomCount 2)

Reading two extra (isolated) bottom ports `0, 1` alongside the survivors: the extraction is still
flip-invariant, confirming the survival is not an artifact of the boundary count. -/

/-- The reassociated double-index conjunct at `bottomCount = 2` (boundary nodes `[0, 1, 5, 6]`). -/
private theorem arcFlip_boundaryRelReassoc2 :
    ∀ firstIndex, firstIndex < 2 + arcFlipRedexCore.openWires.length →
      ∀ secondIndex, secondIndex < 2 + arcFlipRedexCore.openWires.length →
        boundarySameComponent 2 arcFlipRedexCore firstIndex secondIndex
          = boundarySameComponent 2 arcFlipReductCore firstIndex secondIndex := by
  decide

/-- The full partition view agrees at `bottomCount = 2` (a wider boundary than r4 ever sampled). -/
theorem arcFlip_samePartition2 : SameArcPartition 2 arcFlipRedexCore arcFlipReductCore :=
  ⟨by decide, by decide,
    fun firstIndex secondIndex firstInRange secondInRange =>
      arcFlip_boundaryRelReassoc2 firstIndex firstInRange secondIndex secondInRange,
    by decide, by decide⟩

/-- ★ **The arc extraction survives the flip at `bottomCount = 2` too.**  The robustness variant of
`arcFlip_extractsEqual0`: flip-invariance of the observable holds independently of how many bottom
ports are read. -/
theorem arcFlip_extractsEqual2 :
    extractArc 2 arcFlipRedexCore = extractArc 2 arcFlipReductCore :=
  extractArc_eq_of_sameArcPartition 2 arcFlipRedexCore arcFlipReductCore
    arcFlip_samePartition2 (by decide) (by decide)

/-! ## Honesty markers -/

/-- **Honesty marker — the arc extraction SURVIVES the root flip (the non-vacuity terminal is proved).**
`arcFlip_extractsEqual0` proves `extractArc 0` is EQUAL across the two counit/cap run orders at the very
state where `not_arcGodementCoreSwapSimCount_adjunction` refutes the ROOT-level vehicle, via the FULL
`SameArcPartition` (`arcFlip_samePartition0` — r4's three samples promoted to the whole partition datum)
lifted through `extractArc_eq_of_sameArcPartition`; `arcFlip_extractsEqual2` confirms robustness at a
wider boundary.  So the flip is a VEHICLE failure, not a soundness failure: the component route delivers
the observable equality the surgery exists to preserve, exactly at the root vehicle's death site.
`= true`. -/
def fxMode_hasArcRootFlipExtractionSurvival : Bool := true

/-- **Honesty pin — this certificate is CONSISTENT with the r4 refutation, not a re-opening.**  The
imported `fxMode_hasArcCoreSwapSimCountRefuted` STAYS `true`: the root-count vehicle remains machine-
refuted at this flip (`arcFlip_rootsDiverge` restates the `6` vs `5` divergence), and the extraction
survival is delivered by the strictly weaker COMPONENT readout, never by resurrecting `rootComm`.  Root
vehicle dead, extraction alive — the two facts coexist.  `rfl`. -/
theorem arcFlip_coreSwapSimCountRefuted_stays_true :
    fxMode_hasArcCoreSwapSimCountRefuted = true := rfl

/-- **Honesty pin — no standing obligation is flipped by this additive certificate.**  The general
renaming witness `fxMode_hasArcGodementSwapRenameableProof` stays `false` (the Mazurkiewicz independence
over ALL cells is untouched here — this is one concrete witness), and the residual-(2) pin
`fxMode_hasArcGodementSwapRenameableProof2` stays `false`.  The orchestrator must NOT read extraction
survival at one flip as discharging the general witness.  `rfl`. -/
theorem arcFlip_swapRenameableProof2_stays_false :
    fxMode_hasArcGodementSwapRenameableProof2 = false := rfl

end FX1Poly.Polygraph
