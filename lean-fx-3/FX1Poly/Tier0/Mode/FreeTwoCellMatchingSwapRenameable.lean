import FX1Poly.Tier0.Mode.FreeTwoCellSaturatedMatchingGodement
import FX1Poly.Tier0.Mode.FreeTwoCellArcSwapRenameable
import FX1Poly.Tier0.Mode.FreeTwoCellBlockRotation

/-! # mode-3 keystone — the matching-carrier block-swap renaming (the LIVE step-simulation route)

`FreeTwoCellSaturatedMatchingGodement` reduced the whole matching Godement soundness residual to constructing the
renaming `sigma` between the two Godement run orders (`MatchingGodementSwapRenameable`): everything ABOVE the
witness — the fold-decomposition, the partition-view read-off (`extractDiagram_of_matchingRenameRel`), and the
two reductions — is closed.

This file ports the arc route's LIVE count-FREE step-simulation infrastructure to the matching carrier, REUSING
the carrier-agnostic union-find forest / automorphism machinery (`isUnionFindForest`, `unionFindRootOf_unionFindJoin`,
`rootComm_unionFindJoin`, `isUnionFindForest_unionFindJoin`) and the list-map lemmas (`natListInsertAt_map`,
`natListRemoveTwoAt_map`, `natListGetAt_map`, `mapLength`, `mapAppend`, `mapFixedOn`, `droppedWires_map`) that
`FreeTwoCellArcSwapRenameable` already proved over the SHARED primitives.  Because the matching carrier reads ONLY
boundary connectivity (no per-root cup/cap event counts), its simulation invariant `MatchingStepSim` carries SIX
fields (open-wire `sigma`-image, shared `nextFresh`, root automorphism, equal loops, two forests) — the arc's
`ArcStepSimCount` MINUS the two count fields, and STRICTLY LEANER: the cap-MERGE count redistribution (the arc's
genuinely-deferred W8 hard core) is simply ABSENT here.

  ★ `MatchingStepSim` + `matchingStepSim_step` / `_processSpine` / `_runMatchingCell` — the six-field invariant is
    step-stable under a common cup / cap / box, folds over a spine, survives running a cell.  Unlike the arc route
    it needs NO freshness (no count fields), only injectivity + `sigma 0 = 0` (the cap sentinel) + the future-tail
    fixing + the forests it carries.
  ★ `matchingRenameRel_of_matchingStepSim` — reads the five `MatchingRenameRel` fields off the invariant directly
    (the count fields are gone, so this is just the open-wire image + boundary-fixing + the carried `rootComm`).
  ★ `matchingRenameRel_full_of_coreSim` / `MatchingGodementCoreSwapSim` /
    `matchingGodementSwapRenameable_pointwise_of_coreSim` — the suffix-peel and the pointwise parent reduction:
    given the CORE block-swap simulation between the two cores, the common `cellBetaUpper`-then-`rest` suffix peels
    and the full `MatchingRenameRel` reads off.  Sharpens the keystone residual to the explicit block-swap `sigma`
    over arbitrary cells (the genuine Mazurkiewicz independence).
  ★ `runMatchingCell_rightAcc_irrel` — the matching fold ignores the RIGHT whisker context (the residual-(2)
    foundation: `cellAlphaUpper` is the SAME transformer under the redex's `gLow` and the reduct's `gMid`).

Raw Lean 4 + Init; structural / fuel recursion, no `omega` / `simp`-AC / `WellFounded.fix` / `List.append`-lemmas.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Tier0

/-! ## Projection read-offs of the matching cap (its record is wrapped in the same-component `if`) -/

/-- The cap leaves `nextFresh` unchanged (both branches). -/
theorem stepCap_nextFresh (state : WireState) (position : Nat) :
    (stepCap state position).nextFresh = state.nextFresh := by
  dsimp only [stepCap]; split <;> rfl

/-- The cap drops the two wires at `position` (both branches). -/
theorem stepCap_openWires (state : WireState) (position : Nat) :
    (stepCap state position).openWires = natListRemoveTwoAt state.openWires position := by
  dsimp only [stepCap]; split <;> rfl

/-- The cap's links: unchanged when the two read wires are already connected, else their union. -/
theorem stepCap_links (state : WireState) (position : Nat) :
    (stepCap state position).links
      = (if isSameComponent state.links (natListGetAt state.openWires position)
            (natListGetAt state.openWires (position + 1))
          then state.links
          else unionFindJoin state.links (natListGetAt state.openWires position)
            (natListGetAt state.openWires (position + 1))) := by
  dsimp only [stepCap]; split <;> rfl

/-- The cap's loops: incremented exactly when the two read wires were already connected. -/
theorem stepCap_loops (state : WireState) (position : Nat) :
    (stepCap state position).loops
      = (if isSameComponent state.links (natListGetAt state.openWires position)
            (natListGetAt state.openWires (position + 1))
          then state.loops + 1 else state.loops) := by
  dsimp only [stepCap]; split <;> rfl

/-! ## `nextFresh` monotonicity and step-equality -/

/-- One matching step never lowers `nextFresh` (a cup adds 2, a cap adds 0, a box adds its output count). -/
theorem stepAtom_nextFresh_le {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (state : WireState) (atom : SpineAtom signature sourceMode targetMode) :
    state.nextFresh ≤ (stepAtom state atom).nextFresh := by
  unfold stepAtom
  split
  · exact Nat.le_add_right _ _
  · exact Nat.le_of_eq (stepCap_nextFresh state _).symm
  · exact Nat.le_add_right _ _

/-- The whole matching fold never lowers `nextFresh`. -/
theorem processSpine_nextFresh_le {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode} :
    (atoms : List (SpineAtom signature sourceMode targetMode)) → (state : WireState) →
    state.nextFresh ≤ (processSpine state atoms).nextFresh
  | [], _ => Nat.le_refl _
  | atom :: rest, state =>
      Nat.le_trans (stepAtom_nextFresh_le state atom)
        (processSpine_nextFresh_le rest (stepAtom state atom))

/-- Running one cell never lowers `nextFresh`. -/
theorem runMatchingCell_nextFresh_le {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {localSource localTarget : signature.graph.Mode}
    (state : WireState)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    {localDom localCod : ModalityPath signature.graph localSource localTarget}
    (cell : RawTwoCellExpr signature localDom localCod) :
    state.nextFresh ≤ (runMatchingCell state leftAcc rightAcc cell).nextFresh :=
  processSpine_nextFresh_le (cell.spineDiff leftAcc rightAcc []) state

/-- One matching step changes `nextFresh` by an atom-determined amount, so equal `nextFresh` is preserved. -/
theorem stepAtom_nextFresh_eq {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (stateS stateT : WireState) (atom : SpineAtom signature sourceMode targetMode)
    (nfEq : stateS.nextFresh = stateT.nextFresh) :
    (stepAtom stateS atom).nextFresh = (stepAtom stateT atom).nextFresh := by
  unfold stepAtom
  split
  · show stateS.nextFresh + 2 = stateT.nextFresh + 2; rw [nfEq]
  · rw [stepCap_nextFresh, stepCap_nextFresh]; exact nfEq
  · show stateS.nextFresh + _ = stateT.nextFresh + _; rw [nfEq]

/-! ## The fresh-id count is a structural property of the cell (the block widths)

Each block (`cellAlphaUpper`, `cellBeta`) allocates a CONTIGUOUS range of fresh ids whose COUNT depends only on
the cell (its cup / box atoms), NOT on the run order, the position, or the whisker context.  `cellFreshCount`
computes that count structurally; it is the width `w1` / `w2` of the block-rotation window the keystone witness
`sigma = blockRotate lo w1 w2` permutes.  Below we pin `(runMatchingCell …).nextFresh = state.nextFresh +
cellFreshCount cell` and read off the core swap's `nfEq` (one of the six `MatchingStepSim` fields) UNCONDITIONALLY
— the run-order-INDEPENDENCE of the total fresh count. -/

/-- One matching step raises `nextFresh` by exactly the atom's output count `generatorCod.length`: a cup `(0,2)`
allocates `2` (`= |cod|`), a cap `(2,0)` allocates `0` (`= |cod|`), a box allocates `|cod|` — uniform across the
three arms. -/
theorem stepAtom_nextFresh {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (state : WireState) (atom : SpineAtom signature sourceMode targetMode) :
    (stepAtom state atom).nextFresh = state.nextFresh + atom.generatorCod.length := by
  unfold stepAtom
  split
  · rename_i heqCod; rw [heqCod]; rfl
  · rename_i heqCod; rw [stepCap_nextFresh, heqCod]; rfl
  · rfl

/-- The total fresh count of a spine atom list — a right fold of the per-atom output counts, additive over the
cons-only difference list. -/
def atomsFreshTotal {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode} :
    List (SpineAtom signature sourceMode targetMode) → Nat
  | [] => 0
  | atom :: rest => atom.generatorCod.length + atomsFreshTotal rest

/-- The whole matching fold raises `nextFresh` by exactly the spine's total fresh count. -/
theorem processSpine_nextFresh {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode} :
    (atoms : List (SpineAtom signature sourceMode targetMode)) → (state : WireState) →
    (processSpine state atoms).nextFresh = state.nextFresh + atomsFreshTotal atoms
  | [], _ => (Nat.add_zero _).symm
  | atom :: rest, state => by
      show (processSpine (stepAtom state atom) rest).nextFresh
         = state.nextFresh + atomsFreshTotal (atom :: rest)
      rw [processSpine_nextFresh rest (stepAtom state atom), stepAtom_nextFresh]
      show state.nextFresh + atom.generatorCod.length + atomsFreshTotal rest
         = state.nextFresh + (atom.generatorCod.length + atomsFreshTotal rest)
      rw [Nat.add_assoc]

/-- ★ **The fresh-id count of a cell, structurally** (the block width).  A generator counts its arities' fresh
count, identity counts `0`, vertical composites add, whiskerings pass through (context-irrelevant).  Mirrors
`RawTwoCellExpr.size`'s five-case match — constant `Nat` motive, propext-free. -/
def cellFreshCount {signature : ModeSignature} :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RawTwoCellExpr signature sourcePath targetPath → Nat
  | _, _, _, targetPath, .gen _ => targetPath.length
  | _, _, _, _, .id _ => 0
  | _, _, _, _, .vcomp cellAlpha cellBeta => cellFreshCount cellAlpha + cellFreshCount cellBeta
  | _, _, _, _, .whiskerLeft _ body => cellFreshCount body
  | _, _, _, _, .whiskerRight _ body => cellFreshCount body

/-- ★ **The spine's total fresh count factors through `cellFreshCount`, context-independently.**  Folding
`atomsFreshTotal` over `cell.spineDiff leftAcc rightAcc rest` equals `cellFreshCount cell + atomsFreshTotal rest`
for ANY whisker contexts — the arities (hence fresh counts) of a cell's atoms are determined by its generators,
not by `leftAcc` / `rightAcc`.  Structural recursion on the cell, mirroring `spineDiff`. -/
theorem atomsFreshTotal_spineDiff {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {localSource localTarget : signature.graph.Mode} →
    (leftAcc : ModalityPath signature.graph overallSource localSource) →
    (rightAcc : ModalityPath signature.graph localTarget overallTarget) →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    (rest : List (SpineAtom signature overallSource overallTarget)) →
    atomsFreshTotal (cell.spineDiff leftAcc rightAcc rest) = cellFreshCount cell + atomsFreshTotal rest
  | _, _, _, _, _, _, .gen _, _ => rfl
  | _, _, _, _, _, _, .id _, _ => (Nat.zero_add _).symm
  | _, _, leftAcc, rightAcc, _, _, .vcomp cellAlpha cellBeta, rest => by
      show atomsFreshTotal (cellAlpha.spineDiff leftAcc rightAcc (cellBeta.spineDiff leftAcc rightAcc rest))
         = cellFreshCount cellAlpha + cellFreshCount cellBeta + atomsFreshTotal rest
      rw [atomsFreshTotal_spineDiff leftAcc rightAcc cellAlpha (cellBeta.spineDiff leftAcc rightAcc rest),
        atomsFreshTotal_spineDiff leftAcc rightAcc cellBeta rest, Nat.add_assoc]
  | _, _, leftAcc, rightAcc, _, _, .whiskerLeft oneCell body, rest =>
      atomsFreshTotal_spineDiff (composePath leftAcc oneCell) rightAcc body rest
  | _, _, leftAcc, rightAcc, _, _, .whiskerRight oneCell body, rest =>
      atomsFreshTotal_spineDiff leftAcc (composePath oneCell rightAcc) body rest

/-- ★ **Running a cell raises `nextFresh` by exactly `cellFreshCount cell`** — context-independently. -/
theorem runMatchingCell_nextFresh {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {localSource localTarget : signature.graph.Mode}
    (state : WireState)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    {localDom localCod : ModalityPath signature.graph localSource localTarget}
    (cell : RawTwoCellExpr signature localDom localCod) :
    (runMatchingCell state leftAcc rightAcc cell).nextFresh = state.nextFresh + cellFreshCount cell := by
  show (processSpine state (cell.spineDiff leftAcc rightAcc [])).nextFresh = state.nextFresh + cellFreshCount cell
  rw [processSpine_nextFresh, atomsFreshTotal_spineDiff]
  show state.nextFresh + (cellFreshCount cell + 0) = state.nextFresh + cellFreshCount cell
  rfl

/-- ★ **The core swap's `nfEq` field, UNCONDITIONALLY.**  The two cores allocate the SAME total fresh count
(`cellFreshCount cellAlphaUpper + cellFreshCount cellBeta`) on top of the common post-`cellAlpha` counter, only in
the opposite block order — so they have equal `nextFresh`.  One of the six `MatchingStepSim` fields of
`MatchingGodementCoreSwapSim`, discharged with NO geometric/locality input (just `runMatchingCell_nextFresh` +
`Nat.add_right_comm`).  Independent of `sigma` — the block rotation's window total `w1 + w2` is order-blind. -/
theorem matchingCoreSwap_nextFresh_eq {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {fLow fMid fHigh : ModalityPath signature.graph sourceMode middleMode}
    {gLow gMid : ModalityPath signature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr signature fLow fMid)
    (cellAlphaUpper : RawTwoCellExpr signature fMid fHigh)
    (cellBeta : RawTwoCellExpr signature gLow gMid)
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget)
    (state : WireState) :
    (runMatchingCell (runMatchingCell
        (runMatchingCell state leftAcc (composePath gLow rightAcc) cellAlpha)
        leftAcc (composePath gLow rightAcc) cellAlphaUpper)
      (composePath leftAcc fHigh) rightAcc cellBeta).nextFresh
    = (runMatchingCell (runMatchingCell
        (runMatchingCell state leftAcc (composePath gLow rightAcc) cellAlpha)
        (composePath leftAcc fMid) rightAcc cellBeta)
      leftAcc (composePath gMid rightAcc) cellAlphaUpper).nextFresh := by
  simp only [runMatchingCell_nextFresh]
  rw [Nat.add_right_comm]

/-! ## The union-find FOREST invariant is preserved by every matching step -/

/-- A CUP step preserves the forest invariant — its `links` is a single `unionFindJoin` over `state.links`. -/
theorem isUnionFindForest_stepCup (state : WireState) (position : Nat)
    (hforest : isUnionFindForest state.links) :
    isUnionFindForest (stepCup state position).links := by
  show isUnionFindForest (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
  exact isUnionFindForest_unionFindJoin _ _ _ hforest

/-- A CAP step preserves the forest invariant — its `links` is unchanged or a single `unionFindJoin`. -/
theorem isUnionFindForest_stepCap (state : WireState) (position : Nat)
    (hforest : isUnionFindForest state.links) :
    isUnionFindForest (stepCap state position).links := by
  rw [stepCap_links]
  split
  · exact hforest
  · exact isUnionFindForest_unionFindJoin _ _ _ hforest

/-- One matching step preserves the forest invariant — cup / cap via the join lemmas, box leaves `links` alone. -/
theorem isUnionFindForest_stepAtom {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (state : WireState) (atom : SpineAtom signature sourceMode targetMode)
    (hforest : isUnionFindForest state.links) :
    isUnionFindForest (stepAtom state atom).links := by
  unfold stepAtom
  split
  · exact isUnionFindForest_stepCup state _ hforest
  · exact isUnionFindForest_stepCap state _ hforest
  · exact hforest

/-- The whole matching fold preserves the forest invariant. -/
theorem isUnionFindForest_processSpine {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    (atoms : List (SpineAtom signature sourceMode targetMode)) → (state : WireState) →
    isUnionFindForest state.links → isUnionFindForest (processSpine state atoms).links
  | [], _, hforest => hforest
  | atom :: rest, state, hforest =>
      isUnionFindForest_processSpine rest (stepAtom state atom)
        (isUnionFindForest_stepAtom state atom hforest)

/-- Running one cell preserves the forest invariant. -/
theorem isUnionFindForest_runMatchingCell {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {localSource localTarget : signature.graph.Mode}
    (state : WireState)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    {localDom localCod : ModalityPath signature.graph localSource localTarget}
    (cell : RawTwoCellExpr signature localDom localCod)
    (hforest : isUnionFindForest state.links) :
    isUnionFindForest (runMatchingCell state leftAcc rightAcc cell).links :=
  isUnionFindForest_processSpine (cell.spineDiff leftAcc rightAcc []) state hforest

/-! ## The open-wire list is step-preserved as a `sigma`-image -/

/-- ★ **`bnodeCorr` step-preservation (at the list level).**  The open-wire list of a matching step is a function
of the input open wires, `nextFresh`, and the atom ALONE (not the links), so if the two states' open wires are
pointwise `sigma`-images and `nextFresh` agrees with `sigma` fixing the future tail, the post-step open wires are
again `sigma`-images.  Cup: the splice commutes (`natListInsertAt_map`), the two fresh legs fixed.  Cap: the drop
commutes (`natListRemoveTwoAt_map`).  Box: the input-dropping fold commutes (`droppedWires_map`) and the fresh
output block is fixed (`mapFixedAbove`). -/
theorem stepAtom_openWires_map {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (sigma : Nat → Nat) (stateS stateT : WireState) (atom : SpineAtom signature sourceMode targetMode)
    (openMap : stateT.openWires = stateS.openWires.map sigma)
    (nfEq : stateS.nextFresh = stateT.nextFresh)
    (fixesAbove : ∀ identifier, stateS.nextFresh ≤ identifier → sigma identifier = identifier) :
    (stepAtom stateT atom).openWires = (stepAtom stateS atom).openWires.map sigma := by
  have hleg0 : sigma stateS.nextFresh = stateT.nextFresh := by rw [fixesAbove _ (Nat.le_refl _), nfEq]
  have hleg1 : sigma (stateS.nextFresh + 1) = stateT.nextFresh + 1 := by
    rw [fixesAbove _ (Nat.le_add_right _ _), nfEq]
  unfold stepAtom
  split
  · show natListInsertAt stateT.openWires (atom.leftContext.length) [stateT.nextFresh, stateT.nextFresh + 1]
       = (natListInsertAt stateS.openWires (atom.leftContext.length) [stateS.nextFresh, stateS.nextFresh + 1]).map
          sigma
    rw [natListInsertAt_map]
    show natListInsertAt stateT.openWires (atom.leftContext.length) [stateT.nextFresh, stateT.nextFresh + 1]
       = natListInsertAt (stateS.openWires.map sigma) (atom.leftContext.length)
          [sigma stateS.nextFresh, sigma (stateS.nextFresh + 1)]
    rw [← openMap, hleg0, hleg1]
  · rw [stepCap_openWires, stepCap_openWires, natListRemoveTwoAt_map, ← openMap]
  · have hblk : ((List.range atom.generatorCod.length).map (· + stateS.nextFresh)).map sigma
          = (List.range atom.generatorCod.length).map (· + stateT.nextFresh) := by
      rw [mapFixedAbove sigma stateS.nextFresh fixesAbove _ (mem_mapAdd_ge stateS.nextFresh _)]
      exact congrArg (fun base => (List.range atom.generatorCod.length).map (· + base)) nfEq
    show natListInsertAt
          (Nat.rec stateT.openWires (fun _ shorter => natListRemoveTwoAt shorter atom.leftContext.length)
            atom.generatorDom.length)
          atom.leftContext.length ((List.range atom.generatorCod.length).map (· + stateT.nextFresh))
       = (natListInsertAt
            (Nat.rec stateS.openWires (fun _ shorter => natListRemoveTwoAt shorter atom.leftContext.length)
              atom.generatorDom.length)
            atom.leftContext.length ((List.range atom.generatorCod.length).map (· + stateS.nextFresh))).map sigma
    rw [natListInsertAt_map, droppedWires_map, hblk, openMap]

/-! ## The union-find AUTOMORPHISM (`rootComm`) is step-preserved -/

/-- A CUP step preserves the union-find automorphism property — its `links` is a single join of the fresh legs
`nf, nf+1` (id-identical on both states by equal `nextFresh`, fixed by `sigma`), carried by `rootComm_unionFindJoin`
with `freshLeg_corr` discharging the leg correspondence. -/
theorem stepCup_rootComm (sigma : Nat → Nat) (inj : ∀ a b, sigma a = sigma b → a = b)
    (stateS stateT : WireState)
    (hforestS : isUnionFindForest stateS.links) (hforestT : isUnionFindForest stateT.links)
    (hnf : stateS.nextFresh = stateT.nextFresh)
    (fixesAbove : ∀ identifier, stateS.nextFresh ≤ identifier → sigma identifier = identifier)
    (hRoot : ∀ x, unionFindRootOf stateT.links (sigma x) = sigma (unionFindRootOf stateS.links x))
    (position : Nat) :
    ∀ x, unionFindRootOf (stepCup stateT position).links (sigma x)
      = sigma (unionFindRootOf (stepCup stateS position).links x) := by
  intro x
  have hleg0 : stateT.nextFresh = sigma stateS.nextFresh := freshLeg_corr sigma _ _ hnf fixesAbove 0
  have hleg1 : stateT.nextFresh + 1 = sigma (stateS.nextFresh + 1) := freshLeg_corr sigma _ _ hnf fixesAbove 1
  show unionFindRootOf (unionFindJoin stateT.links stateT.nextFresh (stateT.nextFresh + 1)) (sigma x)
     = sigma (unionFindRootOf (unionFindJoin stateS.links stateS.nextFresh (stateS.nextFresh + 1)) x)
  exact rootComm_unionFindJoin sigma inj stateS.links stateT.links hforestS hforestT
    stateS.nextFresh (stateS.nextFresh + 1) stateT.nextFresh (stateT.nextFresh + 1) hleg0 hleg1 hRoot x

/-- A CAP step preserves the union-find automorphism property — GIVEN the two read wires correspond under `sigma`.
The cap's links are unchanged (same-component branch, `rootComm` is the input) or the join of the two read wires
(carried by `rootComm_unionFindJoin`).  The same-component test agrees on the two states, so they take the same
branch (`beq_congr_inj` + the input `rootComm`). -/
theorem stepCap_rootComm (sigma : Nat → Nat) (inj : ∀ a b, sigma a = sigma b → a = b)
    (stateS stateT : WireState)
    (hforestS : isUnionFindForest stateS.links) (hforestT : isUnionFindForest stateT.links)
    (hRoot : ∀ x, unionFindRootOf stateT.links (sigma x) = sigma (unionFindRootOf stateS.links x))
    (position : Nat)
    (hleftCorr : natListGetAt stateT.openWires position = sigma (natListGetAt stateS.openWires position))
    (hrightCorr :
      natListGetAt stateT.openWires (position + 1) = sigma (natListGetAt stateS.openWires (position + 1))) :
    ∀ x, unionFindRootOf (stepCap stateT position).links (sigma x)
      = sigma (unionFindRootOf (stepCap stateS position).links x) := by
  intro x
  rw [stepCap_links, stepCap_links]
  have htest : isSameComponent stateT.links (natListGetAt stateT.openWires position)
        (natListGetAt stateT.openWires (position + 1))
      = isSameComponent stateS.links (natListGetAt stateS.openWires position)
        (natListGetAt stateS.openWires (position + 1)) := by
    show (unionFindRootOf stateT.links (natListGetAt stateT.openWires position)
            == unionFindRootOf stateT.links (natListGetAt stateT.openWires (position + 1)))
       = (unionFindRootOf stateS.links (natListGetAt stateS.openWires position)
            == unionFindRootOf stateS.links (natListGetAt stateS.openWires (position + 1)))
    rw [hleftCorr, hrightCorr, hRoot, hRoot, beq_congr_inj sigma inj]
  rw [htest]
  split
  · exact hRoot x
  · exact rootComm_unionFindJoin sigma inj stateS.links stateT.links hforestS hforestT
      (natListGetAt stateS.openWires position) (natListGetAt stateS.openWires (position + 1))
      (natListGetAt stateT.openWires position) (natListGetAt stateT.openWires (position + 1))
      hleftCorr hrightCorr hRoot x

/-- ★ **`rootComm` step-preservation (dispatched).**  The union-find automorphism property carries across a common
matching step: cup via `stepCup_rootComm`, cap via `stepCap_rootComm` (its read-wire correspondences from the
open-wire `sigma`-image via `natListGetAt_map`), box leaves `links` untouched. -/
theorem stepAtom_rootComm {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (sigma : Nat → Nat) (inj : ∀ a b, sigma a = sigma b → a = b) (sigmaFixesZero : sigma 0 = 0)
    (stateS stateT : WireState) (atom : SpineAtom signature sourceMode targetMode)
    (forestS : isUnionFindForest stateS.links) (forestT : isUnionFindForest stateT.links)
    (nfEq : stateS.nextFresh = stateT.nextFresh)
    (openMap : stateT.openWires = stateS.openWires.map sigma)
    (fixesAbove : ∀ identifier, stateS.nextFresh ≤ identifier → sigma identifier = identifier)
    (hRoot : ∀ x, unionFindRootOf stateT.links (sigma x) = sigma (unionFindRootOf stateS.links x)) :
    ∀ x, unionFindRootOf (stepAtom stateT atom).links (sigma x)
      = sigma (unionFindRootOf (stepAtom stateS atom).links x) := by
  intro x
  unfold stepAtom
  split
  · exact stepCup_rootComm sigma inj stateS stateT forestS forestT nfEq fixesAbove hRoot
      (atom.leftContext.length) x
  · have hleftCorr : natListGetAt stateT.openWires (atom.leftContext.length)
        = sigma (natListGetAt stateS.openWires (atom.leftContext.length)) := by
      rw [openMap, natListGetAt_map sigma sigmaFixesZero]
    have hrightCorr : natListGetAt stateT.openWires (atom.leftContext.length + 1)
        = sigma (natListGetAt stateS.openWires (atom.leftContext.length + 1)) := by
      rw [openMap, natListGetAt_map sigma sigmaFixesZero]
    exact stepCap_rootComm sigma inj stateS stateT forestS forestT hRoot
      (atom.leftContext.length) hleftCorr hrightCorr x
  · exact hRoot x

/-! ## The loop count is step-preserved (the cap same-component test agrees under `sigma`) -/

/-- ★ **A step preserves the loop-count equality** — GIVEN the read wires correspond under `sigma`.  Cup / box
leave loops untouched; the cap increments iff the two read wires are already in one component, and that boolean
agrees on both states (`beq_congr_inj` over the corresponding wires + `rootComm`). -/
theorem stepAtom_loopsEq {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (sigma : Nat → Nat) (inj : ∀ a b, sigma a = sigma b → a = b)
    (stateS stateT : WireState) (atom : SpineAtom signature sourceMode targetMode)
    (hRoot : ∀ x, unionFindRootOf stateT.links (sigma x) = sigma (unionFindRootOf stateS.links x))
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
      rw [hwireCorr (atom.leftContext.length), hwireCorr (atom.leftContext.length + 1), hRoot, hRoot,
        beq_congr_inj sigma inj]
    rw [hsc, hloops]
  · exact hloops

/-! ## The bundled single-step simulation invariant (count-FREE — the matching carrier's leanness) -/

/-- ★ **The single-step `MatchingRenameRel` simulation invariant.**  The order-INSENSITIVE data preserved by a
common matching step on a `sigma`-renaming-related pair: the open wires are pointwise `sigma`-images, `nextFresh`
is shared, `loops` agree, `sigma` is a union-find AUTOMORPHISM (`rootComm`), and both link lists are forests.  This
is the arc route's `ArcStepSimCount` MINUS its two per-root cup/cap COUNT fields — the matching carrier reads only
boundary connectivity, so the cap-MERGE count redistribution (the arc's genuinely-deferred hard core) is simply
ABSENT.  Six fields. -/
structure MatchingStepSim (sigma : Nat → Nat) (stateS stateT : WireState) : Prop where
  /-- The open wires are pointwise `sigma`-images. -/
  openMap : stateT.openWires = stateS.openWires.map sigma
  /-- The fresh-allocation counters agree. -/
  nfEq : stateS.nextFresh = stateT.nextFresh
  /-- `sigma` is a union-find automorphism. -/
  rootComm : ∀ x, unionFindRootOf stateT.links (sigma x) = sigma (unionFindRootOf stateS.links x)
  /-- The loop counts agree. -/
  loopsEq : stateT.loops = stateS.loops
  /-- The source links form a forest. -/
  forestS : isUnionFindForest stateS.links
  /-- The target links form a forest. -/
  forestT : isUnionFindForest stateT.links

/-- ★ **The simulation invariant is step-stable** — the six-field bundle.  `openMap` via `stepAtom_openWires_map`,
`nfEq` via `stepAtom_nextFresh_eq`, `rootComm` via `stepAtom_rootComm`, `loopsEq` via `stepAtom_loopsEq` (the
read-wire correspondences supplied by the open-wire `sigma`-image), the two forests via `isUnionFindForest_stepAtom`.
Needs only injectivity + `sigma 0 = 0` (the cap sentinel) + the future-tail fixing — NO freshness (no count fields). -/
theorem matchingStepSim_step {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (sigma : Nat → Nat) (inj : ∀ a b, sigma a = sigma b → a = b) (sigmaFixesZero : sigma 0 = 0)
    (stateS stateT : WireState) (atom : SpineAtom signature sourceMode targetMode)
    (fixesAbove : ∀ identifier, stateS.nextFresh ≤ identifier → sigma identifier = identifier)
    (sim : MatchingStepSim sigma stateS stateT) :
    MatchingStepSim sigma (stepAtom stateS atom) (stepAtom stateT atom) where
  openMap := stepAtom_openWires_map sigma stateS stateT atom sim.openMap sim.nfEq fixesAbove
  nfEq := stepAtom_nextFresh_eq stateS stateT atom sim.nfEq
  rootComm := stepAtom_rootComm sigma inj sigmaFixesZero stateS stateT atom sim.forestS sim.forestT sim.nfEq
    sim.openMap fixesAbove sim.rootComm
  loopsEq := stepAtom_loopsEq sigma inj stateS stateT atom sim.rootComm
    (fun index => by rw [sim.openMap, natListGetAt_map sigma sigmaFixesZero stateS.openWires index]) sim.loopsEq
  forestS := isUnionFindForest_stepAtom stateS atom sim.forestS
  forestT := isUnionFindForest_stepAtom stateT atom sim.forestT

/-- ★ **The simulation invariant folds over a whole spine** — structural recursion, threading the strengthened
`fixesAbove` (the fixed range only shrinks as `nextFresh` grows). -/
theorem matchingStepSim_processSpine {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (sigma : Nat → Nat) (inj : ∀ a b, sigma a = sigma b → a = b) (sigmaFixesZero : sigma 0 = 0) :
    (atoms : List (SpineAtom signature sourceMode targetMode)) → (stateS stateT : WireState) →
    (∀ identifier, stateS.nextFresh ≤ identifier → sigma identifier = identifier) →
    MatchingStepSim sigma stateS stateT →
    MatchingStepSim sigma (processSpine stateS atoms) (processSpine stateT atoms)
  | [], _, _, _, sim => sim
  | atom :: rest, stateS, stateT, fixesAbove, sim => by
      show MatchingStepSim sigma (processSpine (stepAtom stateS atom) rest)
        (processSpine (stepAtom stateT atom) rest)
      exact matchingStepSim_processSpine sigma inj sigmaFixesZero rest (stepAtom stateS atom)
        (stepAtom stateT atom)
        (fun identifier idAtLeast =>
          fixesAbove identifier (Nat.le_trans (stepAtom_nextFresh_le stateS atom) idAtLeast))
        (matchingStepSim_step sigma inj sigmaFixesZero stateS stateT atom fixesAbove sim)

/-- ★ **The simulation invariant survives running one cell** — the spine fold over `cell.spineDiff`. -/
theorem matchingStepSim_runMatchingCell {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {localSource localTarget : signature.graph.Mode}
    (sigma : Nat → Nat) (inj : ∀ a b, sigma a = sigma b → a = b) (sigmaFixesZero : sigma 0 = 0)
    (stateS stateT : WireState)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    {localDom localCod : ModalityPath signature.graph localSource localTarget}
    (cell : RawTwoCellExpr signature localDom localCod)
    (fixesAbove : ∀ identifier, stateS.nextFresh ≤ identifier → sigma identifier = identifier)
    (sim : MatchingStepSim sigma stateS stateT) :
    MatchingStepSim sigma (runMatchingCell stateS leftAcc rightAcc cell) (runMatchingCell stateT leftAcc rightAcc cell) :=
  matchingStepSim_processSpine sigma inj sigmaFixesZero (cell.spineDiff leftAcc rightAcc []) stateS stateT
    fixesAbove sim

/-- ★ **The simulation invariant yields the full `MatchingRenameRel` — all FIVE fields.**  `lengthEq` from the
open-wire `sigma`-image (`mapLength`), `loopsEq`/`inj`/`rootComm` straight from the invariant, `bnodeCorr` from the
open-wire image plus the boundary-fixing (`matchingBoundaryNodes` is `range ++ openWires`, the prefix fixed,
`natListGetAt_map`).  No count fields to discharge — strictly leaner than the arc's `arcRenameRel_of_arcStepSimCount`. -/
theorem matchingRenameRel_of_matchingStepSim (bottomCount : Nat) (sigma : Nat → Nat)
    (inj : ∀ a b, sigma a = sigma b → a = b) (sigmaFixesZero : sigma 0 = 0)
    (fixesBoundary : ∀ identifier, identifier < bottomCount → sigma identifier = identifier)
    (stateS stateT : WireState) (sim : MatchingStepSim sigma stateS stateT) :
    MatchingRenameRel bottomCount sigma stateS stateT where
  lengthEq := by rw [sim.openMap, mapLength]
  loopsEq := sim.loopsEq
  inj := inj
  bnodeCorr := by
    intro index _
    have hbnd : matchingBoundaryNodes bottomCount stateT = (matchingBoundaryNodes bottomCount stateS).map sigma := by
      show List.range bottomCount ++ stateT.openWires = (List.range bottomCount ++ stateS.openWires).map sigma
      rw [sim.openMap, mapAppend, mapFixedOn sigma (List.range bottomCount)
        (fun identifier identifierInRange => fixesBoundary identifier (mem_range_imp_lt identifierInRange))]
    rw [hbnd, natListGetAt_map sigma sigmaFixesZero]
  rootComm := sim.rootComm

/-! ## The suffix-peel and the pointwise parent reduction -/

/-- ★ **Suffix-peel: a core `MatchingStepSim` plus the common suffix yields the full `MatchingRenameRel`.**  From a
`MatchingStepSim` between two cores (with `sigma` injective, fixing `0`, the boundary, and the cores' future tail),
run the common `suffixCell`-then-`rest` suffix on both: `matchingStepSim_runMatchingCell` carries the invariant
across the cell (`nextFresh`-monotone shrinking the fixed range), `matchingStepSim_processSpine` across the tail,
and `matchingRenameRel_of_matchingStepSim` discharges all five fields of the two full states. -/
theorem matchingRenameRel_full_of_coreSim {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {cellSource cellTarget : signature.graph.Mode}
    (sigma : Nat → Nat) (inj : ∀ a b, sigma a = sigma b → a = b) (sigmaFixesZero : sigma 0 = 0)
    (bottomCount : Nat)
    (fixesBoundary : ∀ identifier, identifier < bottomCount → sigma identifier = identifier)
    (redexCore reductCore : WireState)
    (leftAccCell : ModalityPath signature.graph overallSource cellSource)
    (rightAccCell : ModalityPath signature.graph cellTarget overallTarget)
    {cellDom cellCod : ModalityPath signature.graph cellSource cellTarget}
    (suffixCell : RawTwoCellExpr signature cellDom cellCod)
    (rest : List (SpineAtom signature overallSource overallTarget))
    (fixesAbove : ∀ identifier, redexCore.nextFresh ≤ identifier → sigma identifier = identifier)
    (coreSim : MatchingStepSim sigma redexCore reductCore) :
    MatchingRenameRel bottomCount sigma
      (processSpine (runMatchingCell redexCore leftAccCell rightAccCell suffixCell) rest)
      (processSpine (runMatchingCell reductCore leftAccCell rightAccCell suffixCell) rest) := by
  have simAfterCell : MatchingStepSim sigma (runMatchingCell redexCore leftAccCell rightAccCell suffixCell)
      (runMatchingCell reductCore leftAccCell rightAccCell suffixCell) :=
    matchingStepSim_runMatchingCell sigma inj sigmaFixesZero redexCore reductCore leftAccCell rightAccCell suffixCell
      fixesAbove coreSim
  have fixesAboveAfterCell : ∀ identifier,
      (runMatchingCell redexCore leftAccCell rightAccCell suffixCell).nextFresh ≤ identifier
        → sigma identifier = identifier :=
    fun identifier idAtLeast =>
      fixesAbove identifier
        (Nat.le_trans (runMatchingCell_nextFresh_le redexCore leftAccCell rightAccCell suffixCell) idAtLeast)
  exact matchingRenameRel_of_matchingStepSim bottomCount sigma inj sigmaFixesZero fixesBoundary _ _
    (matchingStepSim_processSpine sigma inj sigmaFixesZero rest
      (runMatchingCell redexCore leftAccCell rightAccCell suffixCell)
      (runMatchingCell reductCore leftAccCell rightAccCell suffixCell) fixesAboveAfterCell simAfterCell)

/-- ★ **The core block-swap obligation (matching carrier).**  From a FOREST state with `bottomCount ≤ nextFresh`
and `0 < nextFresh`, an injective `sigma` fixing `0`, the bottom boundary, and the redex core's future tail,
together with the `MatchingStepSim` between the redex core (`cellAlphaUpper` then `cellBeta`) and the reduct core
(`cellBeta` then `cellAlphaUpper`).  This bundles everything `matchingRenameRel_full_of_coreSim` needs to peel the
common suffix — the SOLE remaining residual is the explicit block-swap `sigma` (= `blockRotate`) realising this
`MatchingStepSim` over arbitrary cells (the genuine Mazurkiewicz independence). -/
def MatchingGodementCoreSwapSim (signature : ModeSignature) : Prop :=
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

/-- ★ **The pointwise parent reduction.**  Given the core obligation and a FOREST, `0 < nextFresh`, boundary-below
input state, the two full Godement run orders are `MatchingRenameRel`-related — `MatchingGodementSwapRenameable`'s
conclusion at that instance.  The core `MatchingStepSim` is suffix-peeled over the common `cellBetaUpper`-then-`rest`
tail.  (At pathological / non-fresh states the unconditional `MatchingGodementSwapRenameable` is unsatisfiable — a
cup can allocate a colliding id; see the honesty marker — so this reduction is correctly conditioned, mirroring the
arc route's `arcGodementSwapRenameable_pointwise_of_coreSwapSimCount`.) -/
theorem matchingGodementSwapRenameable_pointwise_of_coreSim {signature : ModeSignature}
    (coreSim : MatchingGodementCoreSwapSim signature)
    {overallSource overallTarget : signature.graph.Mode}
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
    (bottomCount : Nat) (state : WireState)
    (bottomLe : bottomCount ≤ state.nextFresh) (stateForest : isUnionFindForest state.links)
    (nfPos : 0 < state.nextFresh) :
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
          (composePath leftAcc fHigh) rightAcc cellBetaUpper) rest) := by
  obtain ⟨sigma, inj, sigmaFixesZero, fixesBoundary, fixesAbove, sim⟩ :=
    coreSim cellAlpha cellAlphaUpper cellBeta leftAcc rightAcc bottomCount state bottomLe stateForest nfPos
  exact ⟨sigma, matchingRenameRel_full_of_coreSim sigma inj sigmaFixesZero bottomCount fixesBoundary _ _
    (composePath leftAcc fHigh) rightAcc cellBetaUpper rest fixesAbove sim⟩

/-! ## Right-context-irrelevance — the residual-(2) foundation -/

/-- One matching step depends only on the atom's `leftContext.length` and its two arities, not on `rightContext`. -/
theorem stepAtom_congr {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (state : WireState) (atom1 atom2 : SpineAtom signature sourceMode targetMode)
    (hpos : atom1.leftContext.length = atom2.leftContext.length)
    (hdom : atom1.generatorDom.length = atom2.generatorDom.length)
    (hcod : atom1.generatorCod.length = atom2.generatorCod.length) :
    stepAtom state atom1 = stepAtom state atom2 := by
  unfold stepAtom
  rw [hpos, hdom, hcod]

/-- ★ **The matching fold IGNORES the right whisker context** (`stepAtom` never reads `rightContext`).  Structural
recursion on the cell; the generator case via `stepAtom_congr`. -/
theorem processSpine_rightAcc_irrel {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {localSource localTarget : signature.graph.Mode} →
    (leftAcc : ModalityPath signature.graph overallSource localSource) →
    (rightAcc1 rightAcc2 : ModalityPath signature.graph localTarget overallTarget) →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    (state : WireState) →
    (rest1 rest2 : List (SpineAtom signature overallSource overallTarget)) →
    (∀ midState, processSpine midState rest1 = processSpine midState rest2) →
    processSpine state (cell.spineDiff leftAcc rightAcc1 rest1)
      = processSpine state (cell.spineDiff leftAcc rightAcc2 rest2)
  | _, _, leftAcc, rightAcc1, rightAcc2, _, _, .gen generator, state, rest1, rest2, hrest => by
      show processSpine (stepAtom state ⟨_, _, leftAcc, _, _, generator, rightAcc1⟩) rest1
         = processSpine (stepAtom state ⟨_, _, leftAcc, _, _, generator, rightAcc2⟩) rest2
      rw [stepAtom_congr state ⟨_, _, leftAcc, _, _, generator, rightAcc1⟩
        ⟨_, _, leftAcc, _, _, generator, rightAcc2⟩ rfl rfl rfl]
      exact hrest _
  | _, _, _, _, _, _, _, .id _, state, rest1, rest2, hrest => hrest state
  | _, _, leftAcc, rightAcc1, rightAcc2, _, _, .vcomp cellLeft cellRight, state, rest1, rest2, hrest => by
      show processSpine state (cellLeft.spineDiff leftAcc rightAcc1 (cellRight.spineDiff leftAcc rightAcc1 rest1))
         = processSpine state (cellLeft.spineDiff leftAcc rightAcc2 (cellRight.spineDiff leftAcc rightAcc2 rest2))
      exact processSpine_rightAcc_irrel leftAcc rightAcc1 rightAcc2 cellLeft state
        (cellRight.spineDiff leftAcc rightAcc1 rest1) (cellRight.spineDiff leftAcc rightAcc2 rest2)
        (fun midState => processSpine_rightAcc_irrel leftAcc rightAcc1 rightAcc2 cellRight midState
          rest1 rest2 hrest)
  | _, _, leftAcc, rightAcc1, rightAcc2, _, _, .whiskerLeft oneCell body, state, rest1, rest2, hrest =>
      processSpine_rightAcc_irrel (composePath leftAcc oneCell) rightAcc1 rightAcc2 body state
        rest1 rest2 hrest
  | _, _, leftAcc, rightAcc1, rightAcc2, _, _, .whiskerRight oneCell body, state, rest1, rest2, hrest =>
      processSpine_rightAcc_irrel leftAcc (composePath oneCell rightAcc1) (composePath oneCell rightAcc2)
        body state rest1 rest2 hrest

/-- ★ **Running one cell is independent of its RIGHT whisker context** — so `cellAlphaUpper` is the SAME
state-transformer under the redex's `gLow` and the reduct's `gMid`.  The first structural reduction the explicit
block-swap `sigma` (the standing residual) builds on. -/
theorem runMatchingCell_rightAcc_irrel {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {localSource localTarget : signature.graph.Mode}
    (state : WireState)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc1 rightAcc2 : ModalityPath signature.graph localTarget overallTarget)
    {localDom localCod : ModalityPath signature.graph localSource localTarget}
    (cell : RawTwoCellExpr signature localDom localCod) :
    runMatchingCell state leftAcc rightAcc1 cell = runMatchingCell state leftAcc rightAcc2 cell :=
  processSpine_rightAcc_irrel leftAcc rightAcc1 rightAcc2 cell state [] [] (fun _ => rfl)

/-! ## Honesty markers -/

/-- **Honesty marker — the matching fold's union-find FOREST invariant is established.**  Reusing the
carrier-agnostic `isUnionFindForest` / `isUnionFindForest_unionFindJoin`, the predicate is preserved by every
matching fold step — cup (one join), cap (zero or one join), box (links untouched) — and the whole fold / cell
(`isUnionFindForest_stepAtom` / `_processSpine` / `_runMatchingCell`).  So every reachable matching-fold state has
acyclic `links`.  `= true`. -/
def fxMode_hasMatchingFoldForestInvariant : Bool := true

/-- **Honesty marker — the count-FREE single-step `MatchingRenameRel` simulation preserves all SIX fields.**
`MatchingStepSim` bundles the order-insensitive invariant (open-wire `sigma`-image, shared `nextFresh`, root
automorphism, equal loops, two forests); `matchingStepSim_step` proves it preserved by a common cup / cap / box
step, `matchingStepSim_processSpine` / `_runMatchingCell` fold it, and `matchingRenameRel_of_matchingStepSim` reads
off the full five-field `MatchingRenameRel` from it.  STRICTLY LEANER than the arc's `ArcStepSimCount`: the two
per-root cup/cap COUNT fields and their cap-MERGE redistribution (the arc's genuinely-deferred W8 hard core) are
ABSENT — the matching carrier reads only boundary connectivity.  No freshness needed (only injectivity, the cap
sentinel `sigma 0 = 0`, and the future-tail fixing).  `= true`. -/
def fxMode_hasMatchingStepSimInvariant : Bool := true

/-- **Honesty marker — the suffix-peel and the pointwise parent reduction are assembled.**
`matchingRenameRel_full_of_coreSim` runs the shared `cellBetaUpper`-then-`rest` suffix on the two cores and emits
the full `MatchingRenameRel`; `matchingGodementSwapRenameable_pointwise_of_coreSim` discharges
`MatchingGodementSwapRenameable`'s body at every FOREST, `0 < nextFresh`, boundary-below instance FROM the core
obligation `MatchingGodementCoreSwapSim` (the block-swap simulation between the two cores).  So everything ABOVE
the explicit block-swap `sigma` is now a LIVE, zero-axiom, suffix-peeling route — sharpening the keystone residual
to exactly that `sigma`.  `= true`. -/
def fxMode_hasMatchingRenameRelSuffixPeel : Bool := true

/-- **Honesty marker — a residual-(2) FOUNDATION is shipped: right-context-irrelevance.**
`runMatchingCell_rightAcc_irrel` proves the matching fold ignores the RIGHT whisker context (`stepAtom` reads only
`leftContext.length` and the two arities — `stepAtom_congr`), so `cellAlphaUpper` is the SAME transformer under the
redex's `gLow` and the reduct's `gMid`.  This collapses the f-region block's redex/reduct difference to its
left-context shift (`fHigh` vs `fMid`) alone — the first structural reduction the explicit block-swap `sigma`
builds on.  `= true`. -/
def fxMode_hasMatchingRightContextIrrelevance : Bool := true

/-- **Honesty marker — the block widths are pinned and the core swap's `nfEq` field is proven UNCONDITIONALLY.**
`cellFreshCount` computes a cell's contiguous fresh-id allocation count structurally (the block width `w1` / `w2`
of the keystone witness `sigma = blockRotate lo w1 w2`), `runMatchingCell_nextFresh` proves `(runMatchingCell
…).nextFresh = state.nextFresh + cellFreshCount cell` (context-INDEPENDENT, via `atomsFreshTotal_spineDiff`), and
`matchingCoreSwap_nextFresh_eq` reads off the core swap's `nfEq` (one of the six `MatchingStepSim` fields) with NO
geometric/locality input — the total fresh count is run-order-blind (`Nat.add_right_comm`).  So of the six core
fields, `nfEq` (here) and the two forests (`isUnionFindForest_runMatchingCell` from the input forest) are now
discharged GENERICALLY; the genuine Mazurkiewicz residual is the remaining three — `openMap`, `rootComm`,
`loopsEq` — under the block rotation.  `= true`. -/
def fxMode_hasMatchingBlockWidthCount : Bool := true

/-- **Honesty marker — the block-swap WITNESS over arbitrary cells is NOT proven; this is the standing residual,
AND the unconditional parent is refuted at non-fresh states.**  The infrastructure above sharpens the keystone
soundness residual to the SINGLE obligation `MatchingGodementCoreSwapSim`: construct the explicit block-swap
`sigma` (= `blockRotate lo w1 w2`, `lo` the post-`cellAlpha` fresh counter, `w1`/`w2` the structural fresh-id
counts of `cellAlphaUpper` / `cellBeta`) realising the `MatchingStepSim` between the redex core
(`cellAlphaUpper` then `cellBeta`) and the reduct core (`cellBeta` then `cellAlphaUpper`).  Its `openMap` field
(reduct core open wires = the block-swapped image of the redex core's) and `rootComm` field (the block rotation is
a union-find automorphism between the two cores' links) are the genuine Mazurkiewicz independence: they need an
INTERCHANGE-COMMUTATION lemma — that two cells acting at disjoint wire windows commute up to the block rotation of
their disjoint fresh ranges — which in turn rests on a LOCALITY characterisation of `runMatchingCell` (each block
only touches its window's wires and only joins ids in its window + fresh range).  That lemma is unproven; the
block-rotation arithmetic (`blockRotate_inj` etc.) is the renaming primitive it will consume.

TWO standing facts the orchestrator must respect: (i) the SOLE open node is the `MatchingGodementCoreSwapSim`
witness `sigma`; everything above it (fold-decomposition, partition-view read-off, the step-simulation, the
suffix-peel) is closed and zero-axiom.  (ii) the keystone's `MatchingGodementSwapRenameable` is stated
UNCONDITIONALLY in `state`, but is UNSATISFIABLE at pathological non-fresh states (a cup allocates an id colliding
with a pre-existing wire, asymmetrically between the two run orders) — so the unconditional flip cannot be honest;
closing the keystone additionally requires re-gating the soundness chain (`MatchingGodementCommute`,
`matchingGodementInvariant_of_commute`) on freshness (the soundness states are all reachable-from-initial, hence
fresh), exactly as the arc route's `ArcGodementCoreSwapSimCount` conditions on `ArcStateFresh` + `0 < nextFresh`.
`= false`. -/
def fxMode_hasMatchingCoreSwapSimProof : Bool := false

end FX1Poly.Tier0
