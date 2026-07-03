import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingSwapRenameable

/-! # mode-3 keystone — the COMPONENT-level simulation substrate (the corrected block-swap invariant)

`MatchingSwapObstruction` refuted the ROOT-level `rootComm` fields of `MatchingStepSim` / `MatchingRenameRel`:
`unionFindJoin` points the first argument's root at the second's, so root IDENTITIES are join-order-dependent —
exactly what the Godement transposition permutes.  What IS join-order-invariant is the PARTITION, and the
matching extract only ever reads the partition (`findPartnerScan` compares roots for `==` equality).  This file
ships the corrected invariant: `MatchingComponentSim`, whose `componentComm` field carries the same-component
BOOLEAN correspondence `(root_T (sigma a) == root_T (sigma b)) = (root_S a == root_S b)` instead of the refuted
root-level commutation.

  ★ `componentView_unionFindJoin` — the workhorse: the component view transports through CORRESPONDING joins by
    pure congruence.  Rewriting both sides with `unionFindRootOf_unionFindJoin` and the input correspondence
    leaves four cases, each an INSTANCE of the input correspondence — no injectivity, no root correspondence,
    no freshness.
  ★ `MatchingComponentSim` + `matchingComponentSim_step` / `_processSpine` / `_runMatchingCell` — the six-field
    component-level invariant is step-stable and folds, STRICTLY LEANER than the root-level route: the
    injectivity hypothesis is GONE (it existed only to transport root equality through `sigma`; the component
    view transports the boolean directly).
  ★ `MatchingComponentRenameRel` + `extractDiagram_of_matchingComponentRenameRel` +
    `matchingComponentRenameRel_of_matchingComponentSim` — the four-field rename relation (no `inj`) and the
    matching-extract invariance, through the SHARED `extractDiagram_eq_of_connectivityView`.
  ★ `matchingComponentRenameRel_full_of_coreSim` — the suffix-peel at component level: a core
    `MatchingComponentSim` plus the common suffix yields the full relation.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `WellFounded.fix` / `List.append`-lemmas.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The workhorse — the component view transports through corresponding joins -/

/-- ★ **Corresponding joins preserve the component view.**  Both sides rewrite by the root-after-join
characterization (`unionFindRootOf_unionFindJoin`); the join conditions transport by the input correspondence at
`(firstNode, a)` / `(firstNode, b)`; the four resulting branches are each an INSTANCE of the input
correspondence — at `(secondNode, secondNode)`, `(secondNode, b)`, `(a, secondNode)`, `(a, b)`.  No injectivity,
no root-level commutation, no freshness. -/
theorem componentView_unionFindJoin (sigma : Nat → Nat)
    (linksS linksT : List (Nat × Nat))
    (forestS : isUnionFindForest linksS) (forestT : isUnionFindForest linksT)
    (firstNode secondNode : Nat)
    (componentComm : ∀ a b,
      (unionFindRootOf linksT (sigma a) == unionFindRootOf linksT (sigma b))
        = (unionFindRootOf linksS a == unionFindRootOf linksS b))
    (a b : Nat) :
    (unionFindRootOf (unionFindJoin linksT (sigma firstNode) (sigma secondNode)) (sigma a)
        == unionFindRootOf (unionFindJoin linksT (sigma firstNode) (sigma secondNode)) (sigma b))
      = (unionFindRootOf (unionFindJoin linksS firstNode secondNode) a
        == unionFindRootOf (unionFindJoin linksS firstNode secondNode) b) := by
  rw [unionFindRootOf_unionFindJoin linksT (sigma firstNode) (sigma secondNode) (sigma a) forestT,
    unionFindRootOf_unionFindJoin linksT (sigma firstNode) (sigma secondNode) (sigma b) forestT,
    unionFindRootOf_unionFindJoin linksS firstNode secondNode a forestS,
    unionFindRootOf_unionFindJoin linksS firstNode secondNode b forestS,
    componentComm firstNode a, componentComm firstNode b]
  cases hfirstA : unionFindRootOf linksS firstNode == unionFindRootOf linksS a with
  | true =>
      cases hfirstB : unionFindRootOf linksS firstNode == unionFindRootOf linksS b with
      | true => exact componentComm secondNode secondNode
      | false => exact componentComm secondNode b
  | false =>
      cases hfirstB : unionFindRootOf linksS firstNode == unionFindRootOf linksS b with
      | true => exact componentComm a secondNode
      | false => exact componentComm a b

/-! ## The corrected six-field invariant -/

/-- ★ **The component-level single-step simulation invariant** — the corrected form of the refuted
`MatchingStepSim`.  Identical except for the fourth field: `componentComm` carries the same-component BOOLEAN
correspondence instead of root-level commutation, which the join-order swap falsifies
(`not_matchingGodementCoreSwapSimFresh`). -/
structure MatchingComponentSim (sigma : Nat → Nat) (stateS stateT : WireState) : Prop where
  /-- The open wires are pointwise `sigma`-images. -/
  openMap : stateT.openWires = stateS.openWires.map sigma
  /-- The fresh-allocation counters agree. -/
  nfEq : stateS.nextFresh = stateT.nextFresh
  /-- The same-component booleans correspond under `sigma` — the partition view, join-order-invariant. -/
  componentComm : ∀ a b,
    (unionFindRootOf stateT.links (sigma a) == unionFindRootOf stateT.links (sigma b))
      = (unionFindRootOf stateS.links a == unionFindRootOf stateS.links b)
  /-- The loop counts agree. -/
  loopsEq : stateT.loops = stateS.loops
  /-- The source links form a forest. -/
  forestS : isUnionFindForest stateS.links
  /-- The target links form a forest. -/
  forestT : isUnionFindForest stateT.links

/-! ## Step preservation — cup / cap / box -/

/-- A CUP step preserves the component view: its links are a single join of the fresh legs `nf, nf+1`
(id-identical on both states by equal `nextFresh`, fixed by `sigma` via `freshLeg_corr`), carried by
`componentView_unionFindJoin`. -/
theorem stepCup_componentComm (sigma : Nat → Nat) (stateS stateT : WireState)
    (forestS : isUnionFindForest stateS.links) (forestT : isUnionFindForest stateT.links)
    (nfEq : stateS.nextFresh = stateT.nextFresh)
    (fixesAbove : ∀ identifier, stateS.nextFresh ≤ identifier → sigma identifier = identifier)
    (componentComm : ∀ a b,
      (unionFindRootOf stateT.links (sigma a) == unionFindRootOf stateT.links (sigma b))
        = (unionFindRootOf stateS.links a == unionFindRootOf stateS.links b))
    (position : Nat) (a b : Nat) :
    (unionFindRootOf (stepCup stateT position).links (sigma a)
        == unionFindRootOf (stepCup stateT position).links (sigma b))
      = (unionFindRootOf (stepCup stateS position).links a
        == unionFindRootOf (stepCup stateS position).links b) := by
  have legZero : stateT.nextFresh = sigma stateS.nextFresh :=
    freshLeg_corr sigma _ _ nfEq fixesAbove 0
  have legOne : stateT.nextFresh + 1 = sigma (stateS.nextFresh + 1) :=
    freshLeg_corr sigma _ _ nfEq fixesAbove 1
  show (unionFindRootOf (unionFindJoin stateT.links stateT.nextFresh (stateT.nextFresh + 1)) (sigma a)
        == unionFindRootOf (unionFindJoin stateT.links stateT.nextFresh (stateT.nextFresh + 1)) (sigma b))
      = (unionFindRootOf (unionFindJoin stateS.links stateS.nextFresh (stateS.nextFresh + 1)) a
        == unionFindRootOf (unionFindJoin stateS.links stateS.nextFresh (stateS.nextFresh + 1)) b)
  rw [legOne, legZero]
  exact componentView_unionFindJoin sigma stateS.links stateT.links forestS forestT
    stateS.nextFresh (stateS.nextFresh + 1) componentComm a b

/-- A CAP step preserves the component view — GIVEN the two read wires correspond under `sigma`.  The
same-component test agrees on the two states DIRECTLY from the component view (no injectivity transport), so
both take the same branch: unchanged links carry the input, the join branch carries
`componentView_unionFindJoin`. -/
theorem stepCap_componentComm (sigma : Nat → Nat) (stateS stateT : WireState)
    (forestS : isUnionFindForest stateS.links) (forestT : isUnionFindForest stateT.links)
    (componentComm : ∀ a b,
      (unionFindRootOf stateT.links (sigma a) == unionFindRootOf stateT.links (sigma b))
        = (unionFindRootOf stateS.links a == unionFindRootOf stateS.links b))
    (position : Nat)
    (hleftCorr : natListGetAt stateT.openWires position = sigma (natListGetAt stateS.openWires position))
    (hrightCorr :
      natListGetAt stateT.openWires (position + 1) = sigma (natListGetAt stateS.openWires (position + 1)))
    (a b : Nat) :
    (unionFindRootOf (stepCap stateT position).links (sigma a)
        == unionFindRootOf (stepCap stateT position).links (sigma b))
      = (unionFindRootOf (stepCap stateS position).links a
        == unionFindRootOf (stepCap stateS position).links b) := by
  rw [stepCap_links, stepCap_links]
  have htest : isSameComponent stateT.links (natListGetAt stateT.openWires position)
        (natListGetAt stateT.openWires (position + 1))
      = isSameComponent stateS.links (natListGetAt stateS.openWires position)
        (natListGetAt stateS.openWires (position + 1)) := by
    show (unionFindRootOf stateT.links (natListGetAt stateT.openWires position)
            == unionFindRootOf stateT.links (natListGetAt stateT.openWires (position + 1)))
       = (unionFindRootOf stateS.links (natListGetAt stateS.openWires position)
            == unionFindRootOf stateS.links (natListGetAt stateS.openWires (position + 1)))
    rw [hleftCorr, hrightCorr]
    exact componentComm (natListGetAt stateS.openWires position)
      (natListGetAt stateS.openWires (position + 1))
  rw [htest]
  split
  · exact componentComm a b
  · rw [hleftCorr, hrightCorr]
    exact componentView_unionFindJoin sigma stateS.links stateT.links forestS forestT
      (natListGetAt stateS.openWires position) (natListGetAt stateS.openWires (position + 1))
      componentComm a b

/-- ★ **Component-view step-preservation (dispatched).**  Cup via `stepCup_componentComm`, cap via
`stepCap_componentComm` (read-wire correspondences from the open-wire `sigma`-image), box leaves `links`
untouched. -/
theorem stepAtom_componentComm {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (sigma : Nat → Nat) (sigmaFixesZero : sigma 0 = 0)
    (stateS stateT : WireState) (atom : SpineAtom signature sourceMode targetMode)
    (forestS : isUnionFindForest stateS.links) (forestT : isUnionFindForest stateT.links)
    (nfEq : stateS.nextFresh = stateT.nextFresh)
    (openMap : stateT.openWires = stateS.openWires.map sigma)
    (fixesAbove : ∀ identifier, stateS.nextFresh ≤ identifier → sigma identifier = identifier)
    (componentComm : ∀ a b,
      (unionFindRootOf stateT.links (sigma a) == unionFindRootOf stateT.links (sigma b))
        = (unionFindRootOf stateS.links a == unionFindRootOf stateS.links b))
    (a b : Nat) :
    (unionFindRootOf (stepAtom stateT atom).links (sigma a)
        == unionFindRootOf (stepAtom stateT atom).links (sigma b))
      = (unionFindRootOf (stepAtom stateS atom).links a
        == unionFindRootOf (stepAtom stateS atom).links b) := by
  unfold stepAtom
  split
  · exact stepCup_componentComm sigma stateS stateT forestS forestT nfEq fixesAbove componentComm
      atom.leftContext.length a b
  · have hleftCorr : natListGetAt stateT.openWires atom.leftContext.length
        = sigma (natListGetAt stateS.openWires atom.leftContext.length) := by
      rw [openMap, natListGetAt_map sigma sigmaFixesZero]
    have hrightCorr : natListGetAt stateT.openWires (atom.leftContext.length + 1)
        = sigma (natListGetAt stateS.openWires (atom.leftContext.length + 1)) := by
      rw [openMap, natListGetAt_map sigma sigmaFixesZero]
    exact stepCap_componentComm sigma stateS stateT forestS forestT componentComm
      atom.leftContext.length hleftCorr hrightCorr a b
  · exact componentComm a b

/-- ★ **A step preserves the loop-count equality from the component view** — cup / box leave loops untouched;
the cap increments iff its two read wires already share a component, and that boolean agrees on both states
DIRECTLY by `componentComm` over the corresponding wires. -/
theorem stepAtom_loopsEq_ofComponentView {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (sigma : Nat → Nat) (stateS stateT : WireState) (atom : SpineAtom signature sourceMode targetMode)
    (componentComm : ∀ a b,
      (unionFindRootOf stateT.links (sigma a) == unionFindRootOf stateT.links (sigma b))
        = (unionFindRootOf stateS.links a == unionFindRootOf stateS.links b))
    (hwireCorr : ∀ index, natListGetAt stateT.openWires index = sigma (natListGetAt stateS.openWires index))
    (hloops : stateT.loops = stateS.loops) :
    (stepAtom stateT atom).loops = (stepAtom stateS atom).loops := by
  unfold stepAtom
  split
  · exact hloops
  · rw [stepCap_loops, stepCap_loops]
    have hsc : isSameComponent stateT.links (natListGetAt stateT.openWires (atom.leftContext.length))
          (natListGetAt stateT.openWires (atom.leftContext.length + 1))
        = isSameComponent stateS.links (natListGetAt stateS.openWires (atom.leftContext.length))
          (natListGetAt stateS.openWires (atom.leftContext.length + 1)) := by
      show (unionFindRootOf stateT.links (natListGetAt stateT.openWires (atom.leftContext.length))
              == unionFindRootOf stateT.links (natListGetAt stateT.openWires (atom.leftContext.length + 1)))
         = (unionFindRootOf stateS.links (natListGetAt stateS.openWires (atom.leftContext.length))
              == unionFindRootOf stateS.links (natListGetAt stateS.openWires (atom.leftContext.length + 1)))
      rw [hwireCorr (atom.leftContext.length), hwireCorr (atom.leftContext.length + 1)]
      exact componentComm (natListGetAt stateS.openWires (atom.leftContext.length))
        (natListGetAt stateS.openWires (atom.leftContext.length + 1))
    rw [hsc, hloops]
  · exact hloops

/-! ## The bundled invariant is step-stable and folds -/

/-- ★ **The component-level invariant is step-stable** — needs only the cap sentinel `sigma 0 = 0` and the
future-tail fixing; NO injectivity (the root-level route's `inj` existed only to transport root equality through
`sigma`, which the component view never does). -/
theorem matchingComponentSim_step {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (sigma : Nat → Nat) (sigmaFixesZero : sigma 0 = 0)
    (stateS stateT : WireState) (atom : SpineAtom signature sourceMode targetMode)
    (fixesAbove : ∀ identifier, stateS.nextFresh ≤ identifier → sigma identifier = identifier)
    (sim : MatchingComponentSim sigma stateS stateT) :
    MatchingComponentSim sigma (stepAtom stateS atom) (stepAtom stateT atom) where
  openMap := stepAtom_openWires_map sigma stateS stateT atom sim.openMap sim.nfEq fixesAbove
  nfEq := stepAtom_nextFresh_eq stateS stateT atom sim.nfEq
  componentComm := stepAtom_componentComm sigma sigmaFixesZero stateS stateT atom sim.forestS sim.forestT
    sim.nfEq sim.openMap fixesAbove sim.componentComm
  loopsEq := stepAtom_loopsEq_ofComponentView sigma stateS stateT atom sim.componentComm
    (fun index => by rw [sim.openMap, natListGetAt_map sigma sigmaFixesZero stateS.openWires index])
    sim.loopsEq
  forestS := isUnionFindForest_stepAtom stateS atom sim.forestS
  forestT := isUnionFindForest_stepAtom stateT atom sim.forestT

/-- ★ **The component-level invariant folds over a whole spine** — structural recursion, threading the
strengthened `fixesAbove` (the fixed range only shrinks as `nextFresh` grows). -/
theorem matchingComponentSim_processSpine {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (sigma : Nat → Nat) (sigmaFixesZero : sigma 0 = 0) :
    (atoms : List (SpineAtom signature sourceMode targetMode)) → (stateS stateT : WireState) →
    (∀ identifier, stateS.nextFresh ≤ identifier → sigma identifier = identifier) →
    MatchingComponentSim sigma stateS stateT →
    MatchingComponentSim sigma (processSpine stateS atoms) (processSpine stateT atoms)
  | [], _, _, _, sim => sim
  | atom :: rest, stateS, stateT, fixesAbove, sim => by
      show MatchingComponentSim sigma (processSpine (stepAtom stateS atom) rest)
        (processSpine (stepAtom stateT atom) rest)
      exact matchingComponentSim_processSpine sigma sigmaFixesZero rest (stepAtom stateS atom)
        (stepAtom stateT atom)
        (fun identifier idAtLeast =>
          fixesAbove identifier (Nat.le_trans (stepAtom_nextFresh_le stateS atom) idAtLeast))
        (matchingComponentSim_step sigma sigmaFixesZero stateS stateT atom fixesAbove sim)

/-- ★ **The component-level invariant survives running one cell.** -/
theorem matchingComponentSim_runMatchingCell {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {localSource localTarget : signature.graph.Mode}
    (sigma : Nat → Nat) (sigmaFixesZero : sigma 0 = 0)
    (stateS stateT : WireState)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    {localDom localCod : ModalityPath signature.graph localSource localTarget}
    (cell : RawTwoCellExpr signature localDom localCod)
    (fixesAbove : ∀ identifier, stateS.nextFresh ≤ identifier → sigma identifier = identifier)
    (sim : MatchingComponentSim sigma stateS stateT) :
    MatchingComponentSim sigma (runMatchingCell stateS leftAcc rightAcc cell)
      (runMatchingCell stateT leftAcc rightAcc cell) :=
  matchingComponentSim_processSpine sigma sigmaFixesZero (cell.spineDiff leftAcc rightAcc []) stateS stateT
    fixesAbove sim

/-! ## The corrected rename relation and the matching-extract invariance -/

/-- ★ **The component-level rename relation** — the corrected form of the refuted `MatchingRenameRel`: the
root-level `rootComm` field becomes the same-component correspondence, and the `inj` field is GONE (it existed
only for the root-equality transport `beq_congr_inj`, which the component view subsumes). -/
structure MatchingComponentRenameRel (bottomCount : Nat) (sigma : Nat → Nat)
    (firstState secondState : WireState) : Prop where
  /-- The open-wire counts agree. -/
  lengthEq : secondState.openWires.length = firstState.openWires.length
  /-- The loop counts agree. -/
  loopsEq : secondState.loops = firstState.loops
  /-- Every in-range boundary node of `secondState` is the `sigma`-image of the corresponding one of
  `firstState`. -/
  bnodeCorr : ∀ index, index < bottomCount + firstState.openWires.length →
      natListGetAt (matchingBoundaryNodes bottomCount secondState) index
        = sigma (natListGetAt (matchingBoundaryNodes bottomCount firstState) index)
  /-- The same-component booleans correspond under `sigma`. -/
  componentComm : ∀ a b,
    (unionFindRootOf secondState.links (sigma a) == unionFindRootOf secondState.links (sigma b))
      = (unionFindRootOf firstState.links a == unionFindRootOf firstState.links b)

/-- ★ **Renaming-invariance of the matching extract, component-level.**  Component-related matching states
extract to the SAME `DiagramType` — the boundary same-component booleans agree DIRECTLY by `componentComm` over
the corresponding boundary nodes (the root-level route needed `beq_congr_inj` + injectivity here). -/
theorem extractDiagram_of_matchingComponentRenameRel (bottomCount : Nat) (sigma : Nat → Nat)
    (firstState secondState : WireState)
    (rel : MatchingComponentRenameRel bottomCount sigma firstState secondState) :
    extractDiagram bottomCount firstState = extractDiagram bottomCount secondState := by
  apply extractDiagram_eq_of_connectivityView bottomCount firstState secondState rel.lengthEq.symm
    rel.loopsEq.symm
  intro firstIndex secondIndex firstBelow secondBelow
  show (unionFindRootOf firstState.links
          (natListGetAt (matchingBoundaryNodes bottomCount firstState) firstIndex)
        == unionFindRootOf firstState.links
          (natListGetAt (matchingBoundaryNodes bottomCount firstState) secondIndex))
     = (unionFindRootOf secondState.links
          (natListGetAt (matchingBoundaryNodes bottomCount secondState) firstIndex)
        == unionFindRootOf secondState.links
          (natListGetAt (matchingBoundaryNodes bottomCount secondState) secondIndex))
  rw [rel.bnodeCorr firstIndex firstBelow, rel.bnodeCorr secondIndex secondBelow]
  exact (rel.componentComm
    (natListGetAt (matchingBoundaryNodes bottomCount firstState) firstIndex)
    (natListGetAt (matchingBoundaryNodes bottomCount firstState) secondIndex)).symm

/-- ★ **The component-level invariant yields the full rename relation.**  `lengthEq` from the open-wire
`sigma`-image, `loopsEq` / `componentComm` straight from the invariant, `bnodeCorr` from the open-wire image
plus the boundary-fixing. -/
theorem matchingComponentRenameRel_of_matchingComponentSim (bottomCount : Nat) (sigma : Nat → Nat)
    (sigmaFixesZero : sigma 0 = 0)
    (fixesBoundary : ∀ identifier, identifier < bottomCount → sigma identifier = identifier)
    (stateS stateT : WireState) (sim : MatchingComponentSim sigma stateS stateT) :
    MatchingComponentRenameRel bottomCount sigma stateS stateT where
  lengthEq := by rw [sim.openMap, mapLength]
  loopsEq := sim.loopsEq
  bnodeCorr := by
    intro index _
    have hbnd : matchingBoundaryNodes bottomCount stateT
        = (matchingBoundaryNodes bottomCount stateS).map sigma := by
      show List.range bottomCount ++ stateT.openWires
        = (List.range bottomCount ++ stateS.openWires).map sigma
      rw [sim.openMap, mapAppend, mapFixedOn sigma (List.range bottomCount)
        (fun identifier identifierInRange => fixesBoundary identifier (mem_range_imp_lt identifierInRange))]
    rw [hbnd, natListGetAt_map sigma sigmaFixesZero]
  componentComm := sim.componentComm

/-! ## The suffix-peel at component level -/

/-- ★ **Suffix-peel: a core `MatchingComponentSim` plus the common suffix yields the full rename relation.**
The invariant carries across the shared `suffixCell`-then-`rest` tail (`nextFresh`-monotone shrinking the fixed
range), and the read-off discharges all four fields. -/
theorem matchingComponentRenameRel_full_of_coreSim {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {cellSource cellTarget : signature.graph.Mode}
    (sigma : Nat → Nat) (sigmaFixesZero : sigma 0 = 0)
    (bottomCount : Nat)
    (fixesBoundary : ∀ identifier, identifier < bottomCount → sigma identifier = identifier)
    (redexCore reductCore : WireState)
    (leftAccCell : ModalityPath signature.graph overallSource cellSource)
    (rightAccCell : ModalityPath signature.graph cellTarget overallTarget)
    {cellDom cellCod : ModalityPath signature.graph cellSource cellTarget}
    (suffixCell : RawTwoCellExpr signature cellDom cellCod)
    (rest : List (SpineAtom signature overallSource overallTarget))
    (fixesAbove : ∀ identifier, redexCore.nextFresh ≤ identifier → sigma identifier = identifier)
    (coreSim : MatchingComponentSim sigma redexCore reductCore) :
    MatchingComponentRenameRel bottomCount sigma
      (processSpine (runMatchingCell redexCore leftAccCell rightAccCell suffixCell) rest)
      (processSpine (runMatchingCell reductCore leftAccCell rightAccCell suffixCell) rest) := by
  have simAfterCell : MatchingComponentSim sigma
      (runMatchingCell redexCore leftAccCell rightAccCell suffixCell)
      (runMatchingCell reductCore leftAccCell rightAccCell suffixCell) :=
    matchingComponentSim_runMatchingCell sigma sigmaFixesZero redexCore reductCore leftAccCell rightAccCell
      suffixCell fixesAbove coreSim
  have fixesAboveAfterCell : ∀ identifier,
      (runMatchingCell redexCore leftAccCell rightAccCell suffixCell).nextFresh ≤ identifier
        → sigma identifier = identifier :=
    fun identifier idAtLeast =>
      fixesAbove identifier
        (Nat.le_trans (runMatchingCell_nextFresh_le redexCore leftAccCell rightAccCell suffixCell) idAtLeast)
  exact matchingComponentRenameRel_of_matchingComponentSim bottomCount sigma sigmaFixesZero fixesBoundary _ _
    (matchingComponentSim_processSpine sigma sigmaFixesZero rest
      (runMatchingCell redexCore leftAccCell rightAccCell suffixCell)
      (runMatchingCell reductCore leftAccCell rightAccCell suffixCell) fixesAboveAfterCell simAfterCell)

/-! ## Honesty marker -/

/-- **Honesty marker — the component-level simulation substrate is COMPLETE.**  The corrected invariant
(`MatchingComponentSim`, same-component correspondence instead of the refuted root-level commutation) is
step-stable, folds over spines and cells, reads off to the four-field `MatchingComponentRenameRel` (no `inj`),
transports through corresponding joins by pure congruence (`componentView_unionFindJoin`), and drives the
matching extract (`extractDiagram_of_matchingComponentRenameRel`) — with the suffix-peel
(`matchingComponentRenameRel_full_of_coreSim`) ready for the freshness-conditioned block-swap witness.  What
remains for the keystone's residual 1: the freshness-conditioned chain Props over THIS substrate and the
block-swap witness itself (`sigma = blockRotate`, its `openMap` / `componentComm` / `loopsEq` fields — now TRUE
obligations, per the obstruction file's analysis).  `= true`. -/
def fxMode_hasMatchingComponentSimSubstrate : Bool := true

end FX1Poly.Polygraph
