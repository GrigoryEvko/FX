import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyFrameCollapseB

/-! # mode-3 keystone — Piece I STRAIGHTEN: THE CAST BRIDGE, handedness B (RIGHT snake)

`SpineValleyStraightenCastBridge` shipped THE CAST BRIDGE for handedness A (the LEFT snake): the merged cup / cap
`atomFrame` frames collapse to the identity on the shared boundary `leftContext · L · rightContext`.
`SpineValleyFrameCollapseB` shipped the co/op mirror at the ITERATED-whisker leg presentation
(`generalContextFrameLegsCollapseB` : `sharedLegCupLegB ⊟ sharedLegCapLegB ≈ id`).

★ **This file assembles THE CAST BRIDGE for handedness B** — the co/op mirror of `SpineValleyStraightenCastBridge`,
feeding the shipped `generalContextFrameLegsCollapseB`.  The RIGHT-snake shared leg is `R = singletonModalityPath
right`; the merged frames the readback's `atomFrame` produces for a RIGHT-snake shared-leg partner are

  * `mergedCupFrameB = (leftContext · R) ◁ (rightContext ▷ η)` — the shared leg `R` merged into the cup's LEFT
    context (co/op dual of A's cup, where `L` merges into the cup's RIGHT context);
  * `mergedCapFrameB = leftContext ◁ ((R · rightContext) ▷ ε)` — the shared leg `R` merged into the cap's RIGHT
    context.

and `mergedCupFrameB ⊟ castBoundary(alignB) mergedCapFrameB ≈ id` on the shared boundary `leftContext · R ·
rightContext`.  The proof rides the shipped context-absorption pair (`whiskerLeftAbsorb_convFull` /
`whiskerRightAbsorb_convFull`) that converts each merged frame into its iterated leg up to a `composePath`-assoc
re-anchoring cast, then fires `generalContextFrameLegsCollapseB` transported by ONE honest associativity cast (the
merged cup's shared boundary is LEFT-bracketed `(lc·R)·rc` where the iterated collapse lands RIGHT-bracketed
`lc·(R·rc)` — the strict RV/FM `vcompAssoc` re-bracketing the co/op geometry genuinely carries, threaded, never
posited).  There is NO dagger functor; this is re-proven, not transported (Kelly–Street mate involution / RV Prop
3.3.4 "dual argument").

## What this does NOT close (gates stay `false`)

The CAST BRIDGE for handedness B ONLY, at the abstract merged-frame level.  It does NOT specialize to a concrete
`atomFrame cupAtom` / `atomFrame capAtom` (piece i, the seed specialization), NOR the delete-chain surgery, NOR the
readback `stepConv`.  No gate flag flips; `convOfMapEq` and the fib-3 gate flags stay `false`.  This brick reads NO
`matchingOf` / `partnerIndexOf` / arc structure — the shared-leg shape is the factorization's, not the matching's.

Raw Lean 4 + Init; every proof is the shipped absorb pair + cast algebra + `generalContextFrameLegsCollapseB`.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated
in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private cast helpers (leaf-local, so this file imports only `SpineValleyFrameCollapseB`) -/

/-- Saturated convertibility respects a boundary cast (leaf-local mirror of the Readback helper). -/
private theorem saturatedConvCastCongrB {sourceMode targetMode : AdjunctionMode}
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath adjunctionGraph sourceMode targetMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    {cellAlpha cellBeta : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (conv : SaturatedTwoCellConv cellAlpha cellBeta) :
    SaturatedTwoCellConv (RawTwoCellExpr.castBoundary hsource htarget cellAlpha)
      (RawTwoCellExpr.castBoundary hsource htarget cellBeta) := by
  cases hsource; cases htarget; exact conv

/-- An equality of cells lifts to a saturated convertibility (leaf-local mirror of the Readback helper). -/
private theorem saturatedConvOfEqB {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (cellEq : cellAlpha = cellBeta) : SaturatedTwoCellConv cellAlpha cellBeta :=
  cellEq ▸ SaturatedTwoCellConv.refl cellAlpha

/-- A boundary cast of an identity cell IS the identity at the recast boundary. -/
private theorem castBoundaryIdB {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (boundaryEq : sourcePath = targetPath) :
    RawTwoCellExpr.castBoundary boundaryEq boundaryEq
        (RawTwoCellExpr.id (signature := adjunctionModeSignature) sourcePath)
      = RawTwoCellExpr.id (signature := adjunctionModeSignature) targetPath := by
  cases boundaryEq; rfl

/-- Fusion: a cast-cup vertically composed with a doubly-cast-cap collapses to a single outer cast of the plain
vcomp, provided the inner/outer casts and the outer associativity cast agree on endpoints (all discharged by
`cases`). -/
private theorem vcompCastCollapseB {sourceMode targetMode : AdjunctionMode}
    {pCup pMid pCap pCupSrc pCupTgt pCapSrc pCapTgt : ModalityPath adjunctionGraph sourceMode targetMode}
    (cupLeg : RawTwoCellExpr adjunctionModeSignature pCup pMid)
    (capLeg : RawTwoCellExpr adjunctionModeSignature pMid pCap)
    (hCupSrc : pCup = pCupSrc) (hCupTgt : pMid = pCupTgt)
    (hCapSrc : pMid = pCapSrc) (hCapTgt : pCap = pCapTgt)
    (hAlign : pCapSrc = pCupTgt) (hEnd : pCapTgt = pCupSrc)
    (hAssocSrc : pCup = pCupSrc) (hAssocTgt : pCap = pCupSrc) :
    RawTwoCellExpr.vcomp (RawTwoCellExpr.castBoundary hCupSrc hCupTgt cupLeg)
        (RawTwoCellExpr.castBoundary hAlign hEnd
          (RawTwoCellExpr.castBoundary hCapSrc hCapTgt capLeg))
      = RawTwoCellExpr.castBoundary hAssocSrc hAssocTgt
          (RawTwoCellExpr.vcomp cupLeg capLeg) := by
  cases hCupTgt; cases hCapSrc; cases hCapTgt; cases hCupSrc; cases hEnd; rfl

section MergedFrameCastBridgeB

variable {leftSourceMode rightTargetMode : AdjunctionMode}
  (leftContext : ModalityPath adjunctionGraph leftSourceMode AdjunctionMode.tip)
  (rightContext : ModalityPath adjunctionGraph AdjunctionMode.base rightTargetMode)

/-! ## The merged frames (the `atomFrame` presentation of a RIGHT-snake shared-leg partner) -/

/-- The merged cup frame `(leftContext · R) ◁ (rightContext ▷ η)` — the shape `atomFrame` produces for a RIGHT-snake
shared-leg cup (its stored left context being `leftContext · R`). -/
def mergedCupFrameB :
    RawTwoCellExpr adjunctionModeSignature
      (composePath (composePath leftContext (singletonModalityPath AdjunctionModality.right))
        (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base) rightContext))
      (composePath (composePath leftContext (singletonModalityPath AdjunctionModality.right))
        (composePath adjunctionLeftThenRight rightContext)) :=
  RawTwoCellExpr.whiskerLeft
    (composePath leftContext (singletonModalityPath AdjunctionModality.right))
    (RawTwoCellExpr.whiskerRight rightContext adjunctionUnitTwoCell)

/-- The merged cap frame `leftContext ◁ ((R · rightContext) ▷ ε)` — the shape `atomFrame` produces for a RIGHT-snake
shared-leg cap (its stored right context being `R · rightContext`). -/
def mergedCapFrameB :
    RawTwoCellExpr adjunctionModeSignature
      (composePath leftContext
        (composePath adjunctionRightThenLeft
          (composePath (singletonModalityPath AdjunctionModality.right) rightContext)))
      (composePath leftContext
        (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
          (composePath (singletonModalityPath AdjunctionModality.right) rightContext))) :=
  RawTwoCellExpr.whiskerLeft leftContext
    (RawTwoCellExpr.whiskerRight
      (composePath (singletonModalityPath AdjunctionModality.right) rightContext)
      adjunctionCounitTwoCell)

/-! ## The alignment / endpoint casts -/

/-- The alignment cast: the merged cap frame's SOURCE equals the merged cup frame's TARGET — the SAME word
`leftContext R L R rightContext`, differently bracketed (`composePath`-associativity of the `leftContext · R`
prefix). -/
theorem mergedFramesAlignB :
    composePath leftContext
        (composePath adjunctionRightThenLeft
          (composePath (singletonModalityPath AdjunctionModality.right) rightContext))
      = composePath (composePath leftContext (singletonModalityPath AdjunctionModality.right))
        (composePath adjunctionLeftThenRight rightContext) :=
  (composePath_assoc leftContext (singletonModalityPath AdjunctionModality.right)
    (composePath adjunctionLeftThenRight rightContext)).symm

/-- The endpoint cast: the merged cap frame's TARGET equals the shared boundary `leftContext · R · rightContext`
(the merged cup frame's source) — again `composePath`-associativity of the `leftContext · R` prefix. -/
theorem mergedFramesEndpointB :
    composePath leftContext
        (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
          (composePath (singletonModalityPath AdjunctionModality.right) rightContext))
      = composePath (composePath leftContext (singletonModalityPath AdjunctionModality.right))
        (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base) rightContext) :=
  (composePath_assoc leftContext (singletonModalityPath AdjunctionModality.right)
    (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base) rightContext)).symm

/-! ## THE CAST BRIDGE — the merged RIGHT-snake shared-leg frames collapse to the identity -/

/-- ★★ **THE CAST BRIDGE (handedness B).**  The merged cup and cap frames collapse to the identity on the shared
boundary `leftContext · R · rightContext`: `mergedCupFrameB ⊟ castBoundary(alignB) mergedCapFrameB ≈ id`.  The proof
converts each merged frame to its iterated leg by the shipped context-absorption pair, then fires the shipped
cast-free `generalContextFrameLegsCollapseB` transported by the honest associativity cast (the merged cup's shared
boundary is LEFT-bracketed where the iterated collapse lands RIGHT-bracketed).  Co/op mirror of
`mergedSharedLegFramesCollapse`, re-proven (no dagger functor). -/
theorem mergedSharedLegFramesCollapseB :
    SaturatedTwoCellConv
      (RawTwoCellExpr.vcomp (mergedCupFrameB leftContext rightContext)
        (RawTwoCellExpr.castBoundary (mergedFramesAlignB leftContext rightContext)
          (mergedFramesEndpointB leftContext rightContext) (mergedCapFrameB leftContext rightContext)))
      (RawTwoCellExpr.id (signature := adjunctionModeSignature)
        (composePath (composePath leftContext (singletonModalityPath AdjunctionModality.right))
          (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base) rightContext))) := by
  -- The two absorb lemmas: each shared-leg iterated leg IS the merged frame up to a re-anchoring cast.
  have cupAbsorb := whiskerLeftAbsorb_convFull leftContext
    (singletonModalityPath AdjunctionModality.right) rightContext adjunctionUnitTwoCell
  have capAbsorb := whiskerRightAbsorb_convFull leftContext
    (singletonModalityPath AdjunctionModality.right) rightContext adjunctionCounitTwoCell
  -- Flip them so the merged frame is on the LEFT of the conversion.
  have cupConv := TwoCellConvFull.ofCastLeft _ _ (TwoCellConvFull.symm cupAbsorb)
  have capConv := TwoCellConvFull.ofCastLeft _ _ (TwoCellConvFull.symm capAbsorb)
  -- Replace the left factor (cup) by the cast-of-shared-leg form.
  have leftReplaced := SaturatedTwoCellConv.vcompCongrLeft
    (RawTwoCellExpr.castBoundary (mergedFramesAlignB leftContext rightContext)
      (mergedFramesEndpointB leftContext rightContext) (mergedCapFrameB leftContext rightContext))
    (SaturatedTwoCellConv.ofFull cupConv)
  -- Replace the merged cap inside the right factor's cast, then fuse.
  have capCast := SaturatedTwoCellConv.vcompCongrRight
    (RawTwoCellExpr.castBoundary
      (reassocLeftWhisker leftContext (singletonModalityPath AdjunctionModality.right)
        (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base) rightContext).symm
      (reassocLeftWhisker leftContext (singletonModalityPath AdjunctionModality.right)
        adjunctionLeftThenRight rightContext).symm
      (sharedLegCupLegB leftContext rightContext))
    (saturatedConvCastCongrB (mergedFramesAlignB leftContext rightContext)
      (mergedFramesEndpointB leftContext rightContext) (SaturatedTwoCellConv.ofFull capConv))
  -- The honest associativity cast: the iterated collapse lands on the RIGHT-bracketed boundary G,
  -- the merged cup's shared boundary is the LEFT-bracketed S (same word, differently bracketed).
  have assocGtoS :
      composePath leftContext (composePath (singletonModalityPath AdjunctionModality.right) rightContext)
        = composePath (composePath leftContext (singletonModalityPath AdjunctionModality.right))
          (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base) rightContext) :=
    (composePath_assoc leftContext (singletonModalityPath AdjunctionModality.right) rightContext).symm
  -- Now transport the shipped iterated collapse by the outer associativity cast (both boundaries the same S = G).
  have collapseTransported := saturatedConvCastCongrB assocGtoS assocGtoS
    (generalContextFrameLegsCollapseB leftContext rightContext)
  refine SaturatedTwoCellConv.trans leftReplaced
    (SaturatedTwoCellConv.trans capCast
      (SaturatedTwoCellConv.trans ?residual
        (SaturatedTwoCellConv.trans collapseTransported ?idcast)))
  · exact saturatedConvOfEqB (vcompCastCollapseB (sharedLegCupLegB leftContext rightContext)
      (sharedLegCapLegB leftContext rightContext) _ _ _ _ _ _ assocGtoS assocGtoS)
  · exact saturatedConvOfEqB (castBoundaryIdB assocGtoS)

end MergedFrameCastBridgeB

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — THE CAST BRIDGE (handedness B) is LANDED, in the merged-`atomFrame` readback form.**
`mergedSharedLegFramesCollapseB` proves `mergedCupFrameB ⊟ castBoundary(alignB) mergedCapFrameB ≈ id` on the shared
boundary `leftContext · R · rightContext`, for ARBITRARY whisker words.  The two merged frames ARE the readback's
`atomFrame` shapes for a RIGHT-snake shared-leg cup / cap (`mergedCupFrameB = (leftContext · R) ◁ (rightContext ▷
η)`; `mergedCapFrameB = leftContext ◁ ((R · rightContext) ▷ ε)`).  The proof rides the shipped context-absorption
pair and the shipped `generalContextFrameLegsCollapseB`, transported by ONE honest `composePath`-associativity cast
(the co/op geometry lands the merged cup's shared boundary LEFT-bracketed where the iterated collapse is
RIGHT-bracketed).  Co/op mirror of `mergedSharedLegFramesCollapse` — the mate of the LEFT triangle under the
Kelly–Street mate involution (RV Prop 3.3.4 "dual argument"), RE-PROVEN (no dagger functor).  Reads NO `matchingOf`
/ `partnerIndexOf` / arc structure.

  What this marker does NOT close (gates stay `false`): the atom-INSTANCE specialization (piece i), the delete-chain
  surgery, and the readback `stepConv`.  `convOfMapEq` and the fib-3 gate flags stay `false`.  `= true`. -/
def fxMode_hasSpineValleyStraightenCastBridgeB : Bool := true

end FX1Poly.Polygraph
