import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable

/-! # MODE-COMMUTE — the arc COUNT-field core block-swap residual is FALSE AS STATED (machine-checked cap flip)

`ArcGodementCoreSwapSimCount` (the CORRECTED, count-field core block-swap obligation the W7 refutation of the
LIST-field `ArcGodementCoreSwapSim` called for) was believed to be "one `sigma` away" — its residual (2) framed
as merely constructing the block-swap `sigma` over arbitrary cells, `fxMode_hasArcCountInvariantLiveRoute`
asserting the whole route above the `sigma` is LIVE and satisfiable.  This file **refutes the residual as
stated**: `ArcGodementCoreSwapSimCount adjunctionModeSignature` is FALSE.

**The refutation (the counit / cap join-order ROOT FLIP — the arc twin of `not_matchingGodementCoreSwapSimFresh`).**
Instantiate the residual with `cellAlpha = id_{right·left}`, `cellAlphaUpper = cellBeta = counit` (both caps),
`leftAcc = rightAcc = id_tip`, `gLow = fMid = right·left`, `fHigh = gMid = id_tip`, `bottomCount = 0`, at the
fresh forest state `openWires = [1..6]`, `links = [(1,3),(2,5),(4,6)]`, `nextFresh = 7`.  Both run orders leave
the SAME open wires `[5,6]`, but `unionFindJoin`'s first-root-points-at-second policy leaves the merged
component rooted at `6` under the redex order and at `5` under the reduct order — while wires `5` and `6` both
SURVIVE open.  `ArcStepSimCount.openMap` then pins `sigma 5 = 5` and `sigma 6 = 6`, and `ArcStepSimCount.rootComm`
at `5` forces `unionFindRootOf reduct.links (sigma 5) = sigma (unionFindRootOf redex.links 5)`, i.e. `5 = sigma 6
= 6` — contradiction.  No `sigma` whatsoever realises the ROOT-level `rootComm`, so residual (2) is not
"unconstructed", it is UNSATISFIABLE against the current `ArcStepSimCount`.

The join-order root flip lands on OLD wires `5, 6` (both below the two caps' fresh block), so no re-indexing
`sigma` escapes it — this is a strictly deeper obstruction than the `nextFresh = 0` W7 seed refutation
(`not_arcGodementCoreSwapSim_adjunction`), which the `0 < nextFresh` side-condition already dodged.

**The genuine target survives (the mandated surgery, mirroring the matching lane).**  At the same flip the
COMPONENT view AGREES — `loops` equal, the two survivor ports share a component in BOTH orders
(`boundarySameComponent`), and the per-port turnback COUNTS coincide (`internalEventCountAt = 2` both) — so
`SameArcPartition` holds.  Only the root-level VEHICLE `rootComm` is refuted, exactly as in matching.  The live
route is to weaken `ArcStepSimCount.rootComm` / `ArcRenameRel.rootComm` to COMPONENT-level correspondence
`(root_T (sigma a) == root_T (sigma b)) = (root_S a == root_S b)` (partitions are join-order-invariant, unlike
root ids) — the `MatchingComponentSim.componentComm` pattern.  Under that restatement the block-swap witness
becomes a true obligation; under the current root-level fields it stays refuted.

Raw Lean 4 + Init; the concrete run states are tiny (6 wires, 3 union-find edges, 2 caps), so the `decide` calls
are kernel-cheap — the obstruction-smoke idiom of `not_matchingGodementCoreSwapSimFresh`, NOT a large-cell
decide.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The fresh forest state whose merged component gets DIFFERENT roots under the two run orders -/

/-- The root-flip state: six open wires `[1..6]`, three pre-existing forest edges `1→3`, `2→5`, `4→6`,
`nextFresh = 7`, no prior events — the arc twin of `matchingRootFlipState`, with the cup/cap event lists empty. -/
private def arcRootFlipState : ArcWireState :=
  { openWires := [1, 2, 3, 4, 5, 6], links := [(1, 3), (2, 5), (4, 6)], nextFresh := 7, loops := 0,
    cupEventNodes := [], capEventNodes := [] }

/-- The root-flip state is FRESH — every open wire, link endpoint, and (vacuously) event node sits below
`nextFresh = 7`. -/
private theorem arcRootFlipState_isFresh : ArcStateFresh arcRootFlipState :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- The root-flip state's links form a forest (three disjoint child→parent edges). -/
private theorem arcRootFlipState_isForest : isUnionFindForest arcRootFlipState.links :=
  ⟨rfl, rfl, by decide, rfl, rfl, by decide, rfl, rfl, by decide, True.intro⟩

/-- `cellAlpha` for the root-flip instance: the identity 2-cell on `right·left`. -/
private def arcRootFlipIdentityCell :
    RawTwoCellExpr adjunctionModeSignature adjunctionRightThenLeft adjunctionRightThenLeft :=
  RawTwoCellExpr.id _

/-- The redex core (`counit` cap at the f-window position 0, then `counit` cap at the g-window offset 0) — the
`ArcGodementCoreSwapSimCount` redex specialised at the root-flip instance. -/
private def arcRootFlipRedexCore : ArcWireState :=
  runArcCell (runArcCell
      (runArcCell arcRootFlipState
        (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
        (composePath adjunctionRightThenLeft
          (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip))
        arcRootFlipIdentityCell)
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
      (composePath adjunctionRightThenLeft (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip))
      adjunctionCounitTwoCell)
    (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip))
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
    adjunctionCounitTwoCell

/-- The reduct core (`counit` cap at the g-window offset `|right·left| = 2` FIRST, then at the f-window) — the
`ArcGodementCoreSwapSimCount` reduct specialised at the root-flip instance. -/
private def arcRootFlipReductCore : ArcWireState :=
  runArcCell (runArcCell
      (runArcCell arcRootFlipState
        (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
        (composePath adjunctionRightThenLeft
          (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip))
        arcRootFlipIdentityCell)
      (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip) adjunctionRightThenLeft)
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip) adjunctionCounitTwoCell)
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
    (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip))
    adjunctionCounitTwoCell

/-- Both orders leave the SAME open wires `[5, 6]` — the correspondence pins `sigma` on them. -/
private theorem arcRootFlipRedexCore_openWires : arcRootFlipRedexCore.openWires = [5, 6] := by decide

private theorem arcRootFlipReductCore_openWires : arcRootFlipReductCore.openWires = [5, 6] := by decide

/-- The redex order roots the merged component at `6`. -/
private theorem arcRootFlipRedexCore_rootOfFive :
    unionFindRootOf arcRootFlipRedexCore.links 5 = 6 := by decide

/-- The reduct order roots it at `5`. -/
private theorem arcRootFlipReductCore_rootOfFive :
    unionFindRootOf arcRootFlipReductCore.links 5 = 5 := by decide

/-- ★ **No renaming realises the ROOT-level `ArcStepSimCount` between the two root-flip cores.**  `openMap` pins
`sigma 5 = 5` and `sigma 6 = 6`; `rootComm` at `5` then forces `5 = 6`. -/
private theorem arcRootFlip_hasNoStepSimCount (sigma : Nat → Nat)
    (sim : ArcStepSimCount sigma arcRootFlipRedexCore arcRootFlipReductCore) : False := by
  have openImage : [5, 6] = List.map sigma [5, 6] := by
    have rawImage := sim.openMap
    rw [arcRootFlipReductCore_openWires, arcRootFlipRedexCore_openWires] at rawImage
    exact rawImage
  injection openImage with pinFive tailImage
  injection tailImage with pinSix _
  have rootMoves := sim.rootComm 5
  rw [← pinFive, arcRootFlipReductCore_rootOfFive, arcRootFlipRedexCore_rootOfFive, ← pinSix] at rootMoves
  exact absurd rootMoves (by decide)

/-- ★ **The corrected count-field core block-swap residual is FALSE.**  At the fresh, forest, positive-countered
(`0 < nextFresh`) root-flip state, no `sigma` realises the ROOT-level `ArcStepSimCount` between the two Godement
run orders — the join-order root flip on surviving old wires kills `rootComm`.  So residual (2) of
`fxMode_hasArcCountInvariantLiveRoute` is not "unconstructed" but UNSATISFIABLE as stated; the corrected
component-level restatement is the live route. -/
theorem not_arcGodementCoreSwapSimCount_adjunction :
    ¬ ArcGodementCoreSwapSimCount adjunctionModeSignature := by
  intro coreSwapCount
  obtain ⟨sigma, _, _, _, _, sim⟩ :=
    coreSwapCount arcRootFlipIdentityCell adjunctionCounitTwoCell adjunctionCounitTwoCell
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
      0 arcRootFlipState
      arcRootFlipState_isFresh (by decide) arcRootFlipState_isForest (by decide)
  exact arcRootFlip_hasNoStepSimCount sigma sim

/-! ## Positive control — the genuine SameArcPartition target SURVIVES the flip -/

/-- ★ **The COMPONENT view AGREES at the very flip that refutes the root-level vehicle.**  The two run orders'
cores have equal loop counts, agree on whether the two survivor ports share a component, and agree on the
per-port internal cap-turnback COUNT — the three partition-determined fields `SameArcPartition` reads.  So the
refuted `rootComm` is a VEHICLE failure, not a soundness failure: the target survives, and the mandated surgery
is the component-level restatement (`componentComm`), not abandoning the block swap. -/
theorem arcRootFlip_partitionAgrees :
    arcRootFlipRedexCore.loops = arcRootFlipReductCore.loops
      ∧ boundarySameComponent 0 arcRootFlipRedexCore 0 1
          = boundarySameComponent 0 arcRootFlipReductCore 0 1
      ∧ internalEventCountAt arcRootFlipRedexCore.links
          (boundaryNodesOf 0 arcRootFlipRedexCore) arcRootFlipRedexCore.capEventNodes 0
        = internalEventCountAt arcRootFlipReductCore.links
          (boundaryNodesOf 0 arcRootFlipReductCore) arcRootFlipReductCore.capEventNodes 0 :=
  ⟨by decide, by decide, by decide⟩

/-! ## Honesty markers -/

/-- **Honesty marker — the count-field core block-swap residual is machine-checked FALSE at the cap flip.**
`not_arcGodementCoreSwapSimCount_adjunction` refutes `ArcGodementCoreSwapSimCount adjunctionModeSignature`: the
counit / cap join-order ROOT FLIP at a fresh forest state (roots `6` vs `5` on surviving old wires) kills the
ROOT-level `ArcStepSimCount.rootComm`, so residual (2) — framed by `fxMode_hasArcCountInvariantLiveRoute` as
merely "construct the block-swap `sigma`" — is UNSATISFIABLE as stated, not "one `sigma` away".  The overclaim
was validated only on cup-only instances (the `nextFresh = 0` seed and the cup slack probe); it is false for the
cap case.  `arcRootFlip_partitionAgrees` confirms the genuine `SameArcPartition` target SURVIVES (the component
view agrees), so the mandated surgery is the matching lane's `componentComm` restatement of `rootComm`, not
abandoning the witness.  `= true`. -/
def fxMode_hasArcCoreSwapSimCountRefuted : Bool := true

/-- **Honesty pin — the residual-(2) marker `fxMode_hasArcGodementSwapRenameableProof2` STAYS `false`, now on a
STRONGER footing.**  `ArcSwapRenameable` correctly kept it `false` calling the block-swap `sigma`
"genuinely unconstructed"; this file SHARPENS that to "genuinely REFUTED at the cap flip"
(`not_arcGodementCoreSwapSimCount_adjunction`).  The orchestrator must still NOT flip it — and now cannot, since
the obligation it guards is machine-checked false as stated.  `rfl`. -/
theorem fxMode_hasArcGodementSwapRenameableProof2_eq_false :
    fxMode_hasArcGodementSwapRenameableProof2 = false := rfl

end FX1Poly.Polygraph
