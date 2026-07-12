import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.GodementIndependence
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCompoundBlockTransposition
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable

/-! # MODE-COMMUTE r23 — the per-step whisker-support renaming levers (honest BRANCH (b))

## The adjudication (this round is BRANCH (b) — the sidestep FAILS strictly)

The recon adjudicated: the dispatch's `componentComm` core swap consumes the disjoint-support
commutation at **CELL granularity** (whole cells `runArcCell`-run in two orders), whereas the r19
extract closure lands one dimension lower (single stepCup/stepCross/stepCap transpositions).  The
whole-cell whisker list-equality `reduct.links = renameLinks sigma redex.links` over an unbounded
`runArcCell`-generated cell — the recon's missing ingredient K = `disjointWhiskerSupport` — is the
lane's genuine open work; its FULL zero-axiom proof is the same partition-independence the parent
`GodementIndependence` still leaves at `fxMode_hasArcPartitionCommuteProof = false`.  We do NOT
fabricate a closure of it.

## What THIS file ships (each piece zero-axiom, genuinely consuming the shipped r22 sigma)

The recon's step arm reads: "the step consumes the shipped literal/partition arms (D/E) with sigma
aggregating via r22 (G/H)".  This file FACTORS those per-step arms out of `capCapSwap_componentsCorr`
(where the width-`1`/`1` four-join tower's `renameTower` expanded `renameLinks_unionFindJoin` four
times BY HAND) into the reusable, cell-generic per-atom levers the whole-cell induction consumes:

  ★ `renameLinks_stepCupArc` — how an injective renaming `sigma` pushes through ONE cup step's link
    update: `renameLinks sigma (stepCupArc state pos).links` is the two-join tower over
    `renameLinks sigma state.links` with the three fresh legs renamed.  Thin over the shipped
    `renameLinks_unionFindJoin` (twice).
  ★ `renameLinks_stepCapArc` — the same for ONE cap step (two adjacent open wires merged, one fresh
    event node), the two-join tower over the renamed base links with the two wires and the fresh
    event node renamed.
  ★ `renameLinks_compoundTransposition_stepCupArc` / `_stepCapArc` — the two levers INSTANTIATED at
    the r22 compound sigma `compoundFreshBlockTransposition baseFresh widthA widthB`, discharging the
    injectivity side-condition by r22's `compoundFreshBlockTransposition_injective` (this is the
    genuine consumption of the shipped r22 object — no re-derivation).
  ★ `runArcCell_id` — running an identity cell leaves the state unchanged (`spineDiff (.id _) = []`,
    `foldl [] = state`); the structural base of the whole-cell induction.  `rfl`.
  ★ `disjointWhiskerSupport_id_id` — the BASE CASE of the whisker list-equality: when both whiskered
    cells are identities (allocating nothing into either fresh window) the two run orders collapse to
    the pre-swap state, and the equality IS r22's consumer bridge
    `renameLinks_compoundTransposition_ofBelow` on the below-base state.  This is the exact
    `capCapSwap_componentsCorr`-shaped hook the recon named, fired at the identity corner.
  ★ `renameLinks_stepCupArc_probe` — a concrete `rfl` fire: over base `10` at the (2,3) shape, the
    compound sigma pushed through a real cup step on a below-base state `[(0,1)]` computes to
    `[(10,14),(13,14),(0,1)]` end-to-end (sigma moves the fresh legs `10 -> 13`, `11 -> 14`,
    `12 -> 10` while fixing the old `(0,1)` link).

## What is honest-OPEN (the residual, named for the WP-AMALG-2 arc proper)

`fxMode_hasDisjointWhiskerSupport = false`.  The FULL whole-cell whisker list-equality is NOT proven
here.  What it still needs, precisely:
  (1) the JOINT-STATE simulation across the two run orders — the per-step levers here rename the
      LINKS cleanly, but the induction must simultaneously track that `openWires` and `nextFresh`
      transport along sigma (the cap step reads `natListGetAt openWires position`, so the positional
      discipline enters);
  (2) the horizontal-DISJOINTNESS position discipline — cellLow's atoms fire at positions in its own
      whisker context, cellHigh's in its own, and the two must not overlap (the Godement step's
      context shifts `gLow`/`gMid`, `fHigh`/`fMid` from `ArcGodementCommute`);
  (3) the WIDTH-ALIGNMENT seam `redexCore.nextFresh = baseFresh + widthA + widthB` (r22's noted r23
      seam) feeding `compoundFreshBlockTransposition_fixesAbove`;
  (4) the empty-boundary corner `0 < baseFresh` (the walking-monad `eta` nil-source degeneracy the
      matching keystone documents as its residual).

The refuted-literal honesty pin `fxMode_hasArcGodementSamePartitionFreshProof` (the `:545` guard of
the MACHINE-REFUTED `ArcGodementSamePartitionFresh` `:472`, and its forest-gap refutation) stays
`false` — the live target is the FOREST-gated `ArcGodementSamePartitionFreshForest` only, and it is
NOT this file's concern.  This file flips NO gate.

Raw Lean 4 + Init; every proof is a thin re-export of a shipped renaming-equivariance lemma, a `rfl`
structural computation, or a `cases`-free rewrite chain.  Per-declaration `#assert_no_axioms` +
independent `#print axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The per-step renaming levers — how an injective renaming pushes through one arc step -/

/-- ★ **The cup-step renaming lever.**  An injective renaming `sigma` commutes with the link update of
a single CUP: `stepCupArc` allocates three fresh legs (`nextFresh`, `nextFresh+1`, `nextFresh+2`) and
lays down the two-join tower `unionFindJoin (unionFindJoin links leftLeg rightLeg) eventNode leftLeg`,
so renaming the result is the same two-join tower over the renamed base links with the three legs
renamed.  Thin over the shipped `renameLinks_unionFindJoin` (applied to the outer then the inner
join).  The reusable per-atom form of `capCapSwap_componentsCorr`'s hand-expanded `renameTower`. -/
theorem renameLinks_stepCupArc (sigma : Nat → Nat)
    (isInjective : ∀ firstId secondId, sigma firstId = sigma secondId → firstId = secondId)
    (state : ArcWireState) (position : Nat) :
    renameLinks sigma (stepCupArc state position).links
      = unionFindJoin
          (unionFindJoin (renameLinks sigma state.links)
            (sigma state.nextFresh) (sigma (state.nextFresh + 1)))
          (sigma (state.nextFresh + 2)) (sigma state.nextFresh) := by
  show renameLinks sigma
      (unionFindJoin (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        (state.nextFresh + 2) state.nextFresh)
    = unionFindJoin
        (unionFindJoin (renameLinks sigma state.links)
          (sigma state.nextFresh) (sigma (state.nextFresh + 1)))
        (sigma (state.nextFresh + 2)) (sigma state.nextFresh)
  rw [renameLinks_unionFindJoin sigma isInjective, renameLinks_unionFindJoin sigma isInjective]

/-- ★ **The cap-step renaming lever.**  An injective renaming `sigma` commutes with the link update of
a single CAP: `stepCapArc` merges the two adjacent open wires at `position` and one fresh event node
`nextFresh`, laying down `unionFindJoin (unionFindJoin links leftWire rightWire) eventNode leftWire`,
so renaming the result is the same two-join tower over the renamed base links with the two wires and
the fresh event node renamed.  Thin over `renameLinks_unionFindJoin` (twice). -/
theorem renameLinks_stepCapArc (sigma : Nat → Nat)
    (isInjective : ∀ firstId secondId, sigma firstId = sigma secondId → firstId = secondId)
    (state : ArcWireState) (position : Nat) :
    renameLinks sigma (stepCapArc state position).links
      = unionFindJoin
          (unionFindJoin (renameLinks sigma state.links)
            (sigma (natListGetAt state.openWires position))
            (sigma (natListGetAt state.openWires (position + 1))))
          (sigma state.nextFresh) (sigma (natListGetAt state.openWires position)) := by
  show renameLinks sigma
      (unionFindJoin (unionFindJoin state.links
          (natListGetAt state.openWires position)
          (natListGetAt state.openWires (position + 1)))
        state.nextFresh (natListGetAt state.openWires position))
    = unionFindJoin
        (unionFindJoin (renameLinks sigma state.links)
          (sigma (natListGetAt state.openWires position))
          (sigma (natListGetAt state.openWires (position + 1))))
        (sigma state.nextFresh) (sigma (natListGetAt state.openWires position))
  rw [renameLinks_unionFindJoin sigma isInjective, renameLinks_unionFindJoin sigma isInjective]

/-! ## The levers at the r22 compound sigma — genuine consumption of the shipped object -/

/-- ★ The cup-step lever INSTANTIATED at the r22 compound fresh-block transposition, discharging the
injectivity side-condition by r22's `compoundFreshBlockTransposition_injective`.  The concrete object
the whole-cell induction feeds one cup atom at a time. -/
theorem renameLinks_compoundTransposition_stepCupArc (baseFresh widthA widthB : Nat)
    (state : ArcWireState) (position : Nat) :
    renameLinks (compoundFreshBlockTransposition baseFresh widthA widthB)
        (stepCupArc state position).links
      = unionFindJoin
          (unionFindJoin
            (renameLinks (compoundFreshBlockTransposition baseFresh widthA widthB) state.links)
            (compoundFreshBlockTransposition baseFresh widthA widthB state.nextFresh)
            (compoundFreshBlockTransposition baseFresh widthA widthB (state.nextFresh + 1)))
          (compoundFreshBlockTransposition baseFresh widthA widthB (state.nextFresh + 2))
          (compoundFreshBlockTransposition baseFresh widthA widthB state.nextFresh) :=
  renameLinks_stepCupArc (compoundFreshBlockTransposition baseFresh widthA widthB)
    (fun firstId secondId imagesEqual =>
      compoundFreshBlockTransposition_injective baseFresh widthA widthB firstId secondId imagesEqual)
    state position

/-- ★ The cap-step lever INSTANTIATED at the r22 compound fresh-block transposition, discharging
injectivity by r22.  The concrete object the whole-cell induction feeds one cap atom at a time. -/
theorem renameLinks_compoundTransposition_stepCapArc (baseFresh widthA widthB : Nat)
    (state : ArcWireState) (position : Nat) :
    renameLinks (compoundFreshBlockTransposition baseFresh widthA widthB)
        (stepCapArc state position).links
      = unionFindJoin
          (unionFindJoin
            (renameLinks (compoundFreshBlockTransposition baseFresh widthA widthB) state.links)
            (compoundFreshBlockTransposition baseFresh widthA widthB
              (natListGetAt state.openWires position))
            (compoundFreshBlockTransposition baseFresh widthA widthB
              (natListGetAt state.openWires (position + 1))))
          (compoundFreshBlockTransposition baseFresh widthA widthB state.nextFresh)
          (compoundFreshBlockTransposition baseFresh widthA widthB
            (natListGetAt state.openWires position)) :=
  renameLinks_stepCapArc (compoundFreshBlockTransposition baseFresh widthA widthB)
    (fun firstId secondId imagesEqual =>
      compoundFreshBlockTransposition_injective baseFresh widthA widthB firstId secondId imagesEqual)
    state position

/-! ## The structural base of the whole-cell induction -/

/-- Running an identity cell leaves the state unchanged: `spineDiff (.id _) [] = []` and
`processArcSpine state [] = state`.  The base constructor of a whole-cell `runArcCell` induction. -/
theorem runArcCell_id {signature : ModeSignature}
    {overallSource overallTarget localSource localTarget : signature.graph.Mode}
    (state : ArcWireState)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    (path : ModalityPath signature.graph localSource localTarget) :
    runArcCell state leftAcc rightAcc (RawTwoCellExpr.id path) = state := rfl

/-- ★ **The BASE CASE of the disjoint whisker-support list-equality**, consuming r22's consumer
bridge.  When both whiskered cells are identities (neither allocates into either fresh window), the
two run orders both collapse to the pre-swap `state`, so the target `reduct.links = renameLinks sigma
redex.links` reduces to `state.links = renameLinks (compoundFreshBlockTransposition ..) state.links`
— which is r22's `renameLinks_compoundTransposition_ofBelow` on the below-base state, reversed.  This
is the exact identity-corner of the whole-cell induction. -/
theorem disjointWhiskerSupport_id_id {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {sourceLow targetLow sourceHigh targetHigh : signature.graph.Mode}
    (baseFresh widthA widthB : Nat) (state : ArcWireState)
    (leftAccLow : ModalityPath signature.graph overallSource sourceLow)
    (rightAccLow : ModalityPath signature.graph targetLow overallTarget)
    (leftAccHigh : ModalityPath signature.graph overallSource sourceHigh)
    (rightAccHigh : ModalityPath signature.graph targetHigh overallTarget)
    (pathLow : ModalityPath signature.graph sourceLow targetLow)
    (pathHigh : ModalityPath signature.graph sourceHigh targetHigh)
    (stateBelowBase : ∀ edge ∈ state.links, edge.1 < baseFresh ∧ edge.2 < baseFresh) :
    (runArcCell (runArcCell state leftAccHigh rightAccHigh (RawTwoCellExpr.id pathHigh))
        leftAccLow rightAccLow (RawTwoCellExpr.id pathLow)).links
      = renameLinks (compoundFreshBlockTransposition baseFresh widthA widthB)
          (runArcCell (runArcCell state leftAccLow rightAccLow (RawTwoCellExpr.id pathLow))
            leftAccHigh rightAccHigh (RawTwoCellExpr.id pathHigh)).links := by
  rw [runArcCell_id, runArcCell_id, runArcCell_id, runArcCell_id,
    renameLinks_compoundTransposition_ofBelow baseFresh widthA widthB state.links stateBelowBase]

/-! ## Firing probe -/

/-- ★ **Concrete `rfl` fire of the cup lever at the r22 compound sigma.**  Over base `10` at the (2,3)
shape, pushing the compound sigma through a real cup step on the below-base state `[(0,1)]` computes
end-to-end: the cup allocates legs `10, 11, 12`; sigma moves them `10 -> 13`, `11 -> 14`, `12 -> 10`
(block A `[10,12)` up by `widthB=3`, block B `[12,15)` down by `widthA=2`) while fixing the old link
`(0,1)`, giving `[(10,14),(13,14),(0,1)]`.  A refl-checked non-triviality witness that the machinery
fires on a genuine `stepCupArc` output. -/
theorem renameLinks_stepCupArc_probe :
    renameLinks (compoundFreshBlockTransposition 10 2 3)
        (stepCupArc (ArcWireState.mk [0, 1] [(0, 1)] 10 0 [] []) 0).links
      = [(10, 14), (13, 14), (0, 1)] := rfl

/-! ## Honesty markers -/

/-- **Honesty marker — the per-step whisker-support renaming levers are SHIPPED.**  The two per-atom
levers (`renameLinks_stepCupArc`, `renameLinks_stepCapArc`), their compound-sigma instances consuming
r22's injectivity, the identity structural base (`runArcCell_id`), and the identity-corner base case
consuming r22's below-base bridge — all zero-axiom.  `= true`. -/
def fxMode_hasDisjointWhiskerStepLevers : Bool := true

/-- **Honesty pin — the FULL whole-cell disjoint whisker-support list-equality stays OPEN.**  This
file supplies the per-step renaming levers and the identity base case, but NOT the whole-cell
list-equality `reduct.links = renameLinks sigma redex.links` over an unbounded `runArcCell`-generated
cell (the recon's ingredient K).  Its residual is precisely: the joint openWires/nextFresh simulation
across the two run orders, the horizontal-disjointness position discipline, the width-alignment seam
`nextFresh = baseFresh + widthA + widthB`, and the `0 < baseFresh` empty-boundary corner.  `= false`. -/
def fxMode_hasDisjointWhiskerSupport : Bool := false

/-- **Honesty pin — the refuted same-partition-fresh keystone is NEVER flipped.**  The `:545` guard
of the MACHINE-REFUTED `ArcGodementSamePartitionFresh` (`ArcPartitionCommute.lean:472`) stays `false`
— this file does not touch it; the live target is the FOREST-gated
`ArcGodementSamePartitionFreshForest` only.  `rfl`. -/
theorem arcDisjointWhiskerSupport_samePartitionFresh_stays_open :
    fxMode_hasArcGodementSamePartitionFreshProof = false := rfl

end FX1Poly.Polygraph
