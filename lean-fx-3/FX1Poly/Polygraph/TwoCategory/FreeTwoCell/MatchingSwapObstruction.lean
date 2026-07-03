import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingSwapRenameable
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.Model

/-! # mode-3 keystone — the core block-swap residual is FALSE AS STATED (two machine-checked refutations)

The standing residual `MatchingGodementCoreSwapSim` — and its parent `MatchingGodementSwapRenameable` — are
REFUTED, in two independent ways.  No witness construction can close them; the STATEMENTS need surgery.

**Refutation 1 (the cup collision — no freshness).**  Both Props quantify over every `WireState`.  At a state
whose `openWires` already names the id `nextFresh`, the first cup of each run order allocates that same id, and
the two orders interleave it differently against the pre-existing wire: the redex order ends `[1,2,3,4,1]`, the
reduct order `[3,4,1,2,1]`.  Any renaming with `openWires`-image correspondence must send `1` to BOTH `3` and
`1` — no `sigma` exists (`not_matchingGodementCoreSwapSim`).

**Refutation 2 (the root flip — even UNDER freshness).**  `MatchingStepSim.rootComm` and
`MatchingRenameRel.rootComm` demand ROOT-level commutation `unionFindRootOf T (sigma x) = sigma (unionFindRootOf
S x)`.  But `unionFindJoin` points the first argument's root at the SECOND's, so the final root of a merged
component depends on the JOIN ORDER — exactly what the Godement transposition permutes.  At a perfectly fresh
forest state (six wires, three pre-existing edges, two counit caps) the redex order leaves root `6` where the
reduct order leaves root `5`, and both flipped roots SURVIVE as open wires — so the boundary correspondence pins
`sigma 5 = 5`, `sigma 6 = 6` and `rootComm` forces `5 = 6`
(`not_matchingGodementCoreSwapSimFresh` / `not_matchingGodementSwapRenameableFresh`).

**The corrected target (the surgery this mandates).**  (i) Weaken both `rootComm` fields to COMPONENT-level
correspondence `(root_T (sigma a) == root_T (sigma b)) = (root_S a == root_S b)` — the sole consumer
`extractDiagram_of_matchingRenameRel` only ever compares roots for equality, and partitions (unlike root ids)
ARE join-order-invariant.  (ii) Condition the whole chain (`MatchingGodementCommute` /
`MatchingGodementSwapRenameable` / `MatchingGodementCoreSwapSim`) on `WireStateFresh` — refutation 1 is
freshness-independent of the field strength.  Only then is the block-swap witness a true statement.

Raw Lean 4 + Init; the concrete run states are tiny (≤ 6 wires, ≤ 5 union-find edges), so the `decide` calls are
kernel-cheap — this is the obstruction-smoke idiom of `not_arcGodementSamePartition`, NOT a large-cell decide.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Tier0

/-! ## Refutation 1 — the cup collision at a NON-fresh state

`cellAlpha = id_{id_base}`, `cellAlphaUpper = cellBeta = unit` (cups), all accumulators trivial, `bottomCount = 0`,
and the adversarial state `openWires = [1]` with `nextFresh = 1` — the open wire's id collides with the first
fresh allocation. -/

/-- The adversarial state: the open wire `1` ALREADY names `nextFresh = 1`. -/
private def matchingCupCollisionState : WireState :=
  { openWires := [1], links := [], nextFresh := 1, loops := 0 }

/-- `cellAlpha` for the cup-collision instance: the identity 2-cell on `id_base`. -/
private def cupCollisionIdentityCell :
    RawTwoCellExpr adjunctionModeSignature
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base) :=
  RawTwoCellExpr.id _

/-- The redex core (`unit` at the f-window, then `unit` at the g-window offset by `|leftThenRight| = 2`). -/
private def cupCollisionRedexCore : WireState :=
  runMatchingCell (runMatchingCell
      (runMatchingCell matchingCupCollisionState
        (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
        (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
          (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base))
        cupCollisionIdentityCell)
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
      (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
        (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base))
      adjunctionUnitTwoCell)
    (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base) adjunctionLeftThenRight)
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base) adjunctionUnitTwoCell

/-- The reduct core (`unit` at the g-window offset `0` FIRST, then `unit` at the f-window). -/
private def cupCollisionReductCore : WireState :=
  runMatchingCell (runMatchingCell
      (runMatchingCell matchingCupCollisionState
        (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
        (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
          (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base))
        cupCollisionIdentityCell)
      (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
        (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base))
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base) adjunctionUnitTwoCell)
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
    (composePath adjunctionLeftThenRight (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base))
    adjunctionUnitTwoCell

/-- The redex order interleaves the colliding wire as `[1, 2, 3, 4, 1]`. -/
private theorem cupCollisionRedexCore_openWires : cupCollisionRedexCore.openWires = [1, 2, 3, 4, 1] := by
  decide

/-- The reduct order interleaves it as `[3, 4, 1, 2, 1]`. -/
private theorem cupCollisionReductCore_openWires : cupCollisionReductCore.openWires = [3, 4, 1, 2, 1] := by
  decide

/-- ★ **The standing core block-swap residual is FALSE.**  Instantiated at the cup-collision state, its
`openMap` field forces `sigma 1 = 3` (head position) and `sigma 1 = 1` (last position) simultaneously. -/
theorem not_matchingGodementCoreSwapSim : ¬ MatchingGodementCoreSwapSim adjunctionModeSignature := by
  intro coreSwap
  obtain ⟨sigma, _, _, _, _, sim⟩ :=
    coreSwap cupCollisionIdentityCell adjunctionUnitTwoCell adjunctionUnitTwoCell
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
      0 matchingCupCollisionState (by decide) (by exact True.intro) (by decide)
  have collidingImage : [3, 4, 1, 2, 1] = List.map sigma [1, 2, 3, 4, 1] := by
    rw [← cupCollisionReductCore_openWires, ← cupCollisionRedexCore_openWires]
    exact sim.openMap
  injection collidingImage with headImage tailImage0
  injection tailImage0 with _ tailImage1
  injection tailImage1 with _ tailImage2
  injection tailImage2 with _ tailImage3
  injection tailImage3 with lastImage _
  exact absurd (headImage.trans lastImage.symm) (by decide)

/-! ## Refutation 2 — the root flip at a FRESH forest state

`cellAlpha = id`, `cellAlphaUpper = cellBeta = counit` (caps), six open wires `[1..6]` with three pre-existing
forest edges `1→3`, `2→5`, `4→6`, `nextFresh = 7` — every id fresh-bounded.  The two counit caps merge the same
three components in both orders, but `unionFindJoin`'s first-root-points-at-second policy leaves root `6` in the
redex order and root `5` in the reduct order, while wires `5` and `6` both survive as open wires. -/

/-- The fresh forest state whose merged component gets DIFFERENT roots under the two run orders. -/
private def matchingRootFlipState : WireState :=
  { openWires := [1, 2, 3, 4, 5, 6], links := [(1, 3), (2, 5), (4, 6)], nextFresh := 7, loops := 0 }

/-- The root-flip state is FRESH — every open wire and link endpoint sits below `nextFresh = 7`. -/
private theorem matchingRootFlipState_isFresh : WireStateFresh matchingRootFlipState :=
  ⟨by decide, by decide⟩

/-- The root-flip state's links form a forest (three disjoint child→parent edges). -/
private theorem matchingRootFlipState_isForest : isUnionFindForest matchingRootFlipState.links :=
  ⟨rfl, rfl, by decide, rfl, rfl, by decide, rfl, rfl, by decide, True.intro⟩

/-- `cellAlpha` for the root-flip instance: the identity 2-cell on `right·left`. -/
private def rootFlipIdentityCell :
    RawTwoCellExpr adjunctionModeSignature adjunctionRightThenLeft adjunctionRightThenLeft :=
  RawTwoCellExpr.id _

/-- `cellBetaUpper` for the root-flip instance: the identity 2-cell on `id_tip`. -/
private def rootFlipIdentityNilCell :
    RawTwoCellExpr adjunctionModeSignature
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip) :=
  RawTwoCellExpr.id _

/-- The redex core (`counit` cap at the f-window, then `counit` cap at the g-window offset `0`). -/
private def rootFlipRedexCore : WireState :=
  runMatchingCell (runMatchingCell
      (runMatchingCell matchingRootFlipState
        (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
        (composePath adjunctionRightThenLeft
          (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip))
        rootFlipIdentityCell)
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
      (composePath adjunctionRightThenLeft (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip))
      adjunctionCounitTwoCell)
    (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip))
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip) adjunctionCounitTwoCell

/-- The reduct core (`counit` cap at the g-window offset `|rightThenLeft| = 2` FIRST, then at the f-window). -/
private def rootFlipReductCore : WireState :=
  runMatchingCell (runMatchingCell
      (runMatchingCell matchingRootFlipState
        (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
        (composePath adjunctionRightThenLeft
          (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip))
        rootFlipIdentityCell)
      (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip) adjunctionRightThenLeft)
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip) adjunctionCounitTwoCell)
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
    (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip))
    adjunctionCounitTwoCell

/-- Both orders leave the SAME open wires `[5, 6]` — the correspondence pins `sigma` on them. -/
private theorem rootFlipRedexCore_openWires : rootFlipRedexCore.openWires = [5, 6] := by decide

private theorem rootFlipReductCore_openWires : rootFlipReductCore.openWires = [5, 6] := by decide

/-- The redex order roots the merged component at `6`. -/
private theorem rootFlipRedexCore_rootOfFive : unionFindRootOf rootFlipRedexCore.links 5 = 6 := by decide

/-- The reduct order roots it at `5`. -/
private theorem rootFlipReductCore_rootOfFive : unionFindRootOf rootFlipReductCore.links 5 = 5 := by decide

/-- ★ **No renaming realizes the root-level `MatchingStepSim` between the two root-flip cores.**  `openMap` pins
`sigma 5 = 5` and `sigma 6 = 6`; `rootComm` at `5` then forces `5 = 6`. -/
private theorem rootFlip_hasNoStepSim (sigma : Nat → Nat)
    (sim : MatchingStepSim sigma rootFlipRedexCore rootFlipReductCore) : False := by
  have openImage : [5, 6] = List.map sigma [5, 6] := by
    have rawImage := sim.openMap
    rw [rootFlipReductCore_openWires, rootFlipRedexCore_openWires] at rawImage
    exact rawImage
  injection openImage with pinFive tailImage
  injection tailImage with pinSix _
  have rootMoves := sim.rootComm 5
  rw [← pinFive, rootFlipReductCore_rootOfFive, rootFlipRedexCore_rootOfFive, ← pinSix] at rootMoves
  exact absurd rootMoves (by decide)

/-- ★ **No renaming realizes the root-level `MatchingRenameRel` between the two root-flip cores** — the parent
relation fails the same way through its boundary-node correspondence. -/
private theorem rootFlip_hasNoRenameRel (sigma : Nat → Nat)
    (rel : MatchingRenameRel 0 sigma rootFlipRedexCore rootFlipReductCore) : False := by
  have pinFiveRaw := rel.bnodeCorr 0 (by decide)
  have pinSixRaw := rel.bnodeCorr 1 (by decide)
  rw [show natListGetAt (matchingBoundaryNodes 0 rootFlipReductCore) 0 = 5 by decide,
    show natListGetAt (matchingBoundaryNodes 0 rootFlipRedexCore) 0 = 5 by decide] at pinFiveRaw
  rw [show natListGetAt (matchingBoundaryNodes 0 rootFlipReductCore) 1 = 6 by decide,
    show natListGetAt (matchingBoundaryNodes 0 rootFlipRedexCore) 1 = 6 by decide] at pinSixRaw
  have rootMoves := rel.rootComm 5
  rw [← pinFiveRaw, rootFlipReductCore_rootOfFive, rootFlipRedexCore_rootOfFive, ← pinSixRaw] at rootMoves
  exact absurd rootMoves (by decide)

/-! ## The freshness-conditioned variants are STILL false — the weakening must hit the fields themselves -/

/-- The core block-swap obligation CONDITIONED on freshness — `MatchingGodementCoreSwapSim` verbatim plus
`WireStateFresh state`.  Defined here only to be REFUTED: freshness alone does not rescue the root-level
`rootComm` field. -/
def MatchingGodementCoreSwapSimFresh (signature : ModeSignature) : Prop :=
  ∀ {overallSource overallTarget : signature.graph.Mode}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {fLow fMid fHigh : ModalityPath signature.graph sourceMode middleMode}
    {gLow gMid : ModalityPath signature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr signature fLow fMid)
    (cellAlphaUpper : RawTwoCellExpr signature fMid fHigh)
    (cellBeta : RawTwoCellExpr signature gLow gMid)
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget)
    (bottomCount : Nat) (state : WireState),
    bottomCount ≤ state.nextFresh → isUnionFindForest state.links → 0 < state.nextFresh →
    WireStateFresh state →
    ∃ sigma : Nat → Nat,
      (∀ a b, sigma a = sigma b → a = b)
        ∧ sigma 0 = 0
        ∧ (∀ identifier, identifier < bottomCount → sigma identifier = identifier)
        ∧ (∀ identifier,
            (runMatchingCell (runMatchingCell
                (runMatchingCell state leftAcc (composePath gLow rightAcc) cellAlpha)
                leftAcc (composePath gLow rightAcc) cellAlphaUpper)
              (composePath leftAcc fHigh) rightAcc cellBeta).nextFresh ≤ identifier
            → sigma identifier = identifier)
        ∧ MatchingStepSim sigma
            (runMatchingCell (runMatchingCell
                (runMatchingCell state leftAcc (composePath gLow rightAcc) cellAlpha)
                leftAcc (composePath gLow rightAcc) cellAlphaUpper)
              (composePath leftAcc fHigh) rightAcc cellBeta)
            (runMatchingCell (runMatchingCell
                (runMatchingCell state leftAcc (composePath gLow rightAcc) cellAlpha)
                (composePath leftAcc fMid) rightAcc cellBeta)
              leftAcc (composePath gMid rightAcc) cellAlphaUpper)

/-- ★ **Freshness does NOT rescue the core obligation** — the root-flip state is fresh, a forest, and
positive-countered, yet no `sigma` realizes the root-level simulation between its two run orders. -/
theorem not_matchingGodementCoreSwapSimFresh :
    ¬ MatchingGodementCoreSwapSimFresh adjunctionModeSignature := by
  intro coreSwapFresh
  obtain ⟨sigma, _, _, _, _, sim⟩ :=
    coreSwapFresh rootFlipIdentityCell adjunctionCounitTwoCell adjunctionCounitTwoCell
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
      0 matchingRootFlipState
      (by decide) matchingRootFlipState_isForest (by decide) matchingRootFlipState_isFresh
  exact rootFlip_hasNoStepSim sigma sim

/-- The renaming-level parent CONDITIONED on freshness — `MatchingGodementSwapRenameable` verbatim plus
`WireStateFresh state`.  Defined here only to be REFUTED. -/
def MatchingGodementSwapRenameableFresh (signature : ModeSignature) : Prop :=
  ∀ {overallSource overallTarget : signature.graph.Mode}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {fLow fMid fHigh : ModalityPath signature.graph sourceMode middleMode}
    {gLow gMid gHigh : ModalityPath signature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr signature fLow fMid)
    (cellAlphaUpper : RawTwoCellExpr signature fMid fHigh)
    (cellBeta : RawTwoCellExpr signature gLow gMid)
    (cellBetaUpper : RawTwoCellExpr signature gMid gHigh)
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget)
    (rest : List (SpineAtom signature overallSource overallTarget))
    (bottomCount : Nat) (state : WireState),
    WireStateFresh state →
    ∃ sigma : Nat → Nat, MatchingRenameRel bottomCount sigma
      (processSpine
        (runMatchingCell (runMatchingCell (runMatchingCell
            (runMatchingCell state leftAcc (composePath gLow rightAcc) cellAlpha)
            leftAcc (composePath gLow rightAcc) cellAlphaUpper)
          (composePath leftAcc fHigh) rightAcc cellBeta)
          (composePath leftAcc fHigh) rightAcc cellBetaUpper) rest)
      (processSpine
        (runMatchingCell (runMatchingCell (runMatchingCell
            (runMatchingCell state leftAcc (composePath gLow rightAcc) cellAlpha)
            (composePath leftAcc fMid) rightAcc cellBeta)
          leftAcc (composePath gMid rightAcc) cellAlphaUpper)
          (composePath leftAcc fHigh) rightAcc cellBetaUpper) rest)

/-- ★ **Freshness does NOT rescue the renaming-level parent either** — with `cellBetaUpper = id` and an empty
tail the two full states ARE the root-flip cores, and `MatchingRenameRel`'s root-level `rootComm` fails on them. -/
theorem not_matchingGodementSwapRenameableFresh :
    ¬ MatchingGodementSwapRenameableFresh adjunctionModeSignature := by
  intro swapRenameableFresh
  obtain ⟨sigma, rel⟩ :=
    swapRenameableFresh rootFlipIdentityCell adjunctionCounitTwoCell adjunctionCounitTwoCell
      rootFlipIdentityNilCell
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
      [] 0 matchingRootFlipState matchingRootFlipState_isFresh
  exact rootFlip_hasNoRenameRel sigma rel

/-- ★ **The unconditional renaming-level parent is false** a fortiori — it specializes to the fresh variant. -/
theorem not_matchingGodementSwapRenameable :
    ¬ MatchingGodementSwapRenameable adjunctionModeSignature := by
  intro swapRenameable
  obtain ⟨sigma, rel⟩ :=
    swapRenameable rootFlipIdentityCell adjunctionCounitTwoCell adjunctionCounitTwoCell
      rootFlipIdentityNilCell
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
      [] 0 matchingRootFlipState
  exact rootFlip_hasNoRenameRel sigma rel

/-! ## Honesty marker -/

/-- **Honesty marker — the standing block-swap residual is machine-checked FALSE, two independent ways.**
`not_matchingGodementCoreSwapSim` (the cup collision at a non-fresh state kills `openMap`) and
`not_matchingGodementCoreSwapSimFresh` / `not_matchingGodementSwapRenameableFresh` (the join-order root flip at
a FRESH forest state kills the root-level `rootComm`) close off every witness attempt against the current
statements — including the freshness-gated re-attack the previous honesty notes anticipated.  The mandated
surgery: weaken `MatchingStepSim.rootComm` and `MatchingRenameRel.rootComm` to COMPONENT-level correspondence
(the matching extract only ever compares roots for equality, and partitions are join-order-invariant), AND
condition the soundness chain on `WireStateFresh`.  Under BOTH corrections the block-swap witness becomes a true
obligation; under either alone it stays refuted.  `= true`. -/
def fxMode_hasMatchingCoreSwapObstructions : Bool := true

end FX1Poly.Tier0
