import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyFrameCollapse

/-! # mode-3 keystone — Piece I STRAIGHTEN (ii): the HANDEDNESS-B (RIGHT-snake) general shared-leg frame collapse

`SpineValleyFrameCollapse` discharged Gap 2b for handedness A (the LEFT snake): for arbitrary whisker words the
shared-leg cup and cap legs `sharedLegCupLeg ⊟ sharedLegCapLeg` collapse to the identity on `leftContext · L ·
rightContext`, cast-free, by re-folding into the whiskered LEFT seed snake and firing
`leftSnakeDoubleWhiskerCollapses`.

★ **This file is the co/op MIRROR — handedness B (the RIGHT snake).**  `SpineValleyStraightenFactor`'s width
dichotomy (`zigZagSharedLeg_widthDichotomy`) is `A ∨ B`: a `zigZagSharedLeg` redex is EITHER the left-snake
orientation (`sharedLegFactorHandednessA`, `lcCap = lcCup · L`) OR the right-snake orientation
(`sharedLegFactorHandednessB`, `lcCup = lcCap · R`).  Both are genuinely reachable, so handedness B is ON THE
CRITICAL PATH for the STRAIGHTEN producer's totality — the RIGHT-snake general-context collapse must be built.

There is NO op-duality / dagger functor in this codebase (`adjunctionSeedLeftSnake` and `adjunctionSeedRightSnake`
are separate concrete cells, nothing transports a left construction to the right automatically), so the collapse is
RE-PROVEN, not obtained for free.  But per Riehl–Verity Prop 3.3.4 (arXiv:1310.8279) the two triangle identities
are mates under the op-2-functor / Kelly–Street mate involution (`LAdj ≅ RAdj`), so the re-proof is a mechanical
CLONE of `SpineValleyFrameCollapse`'s handedness-A construction with the shared leg `L = singletonModalityPath
left` replaced by `R = singletonModalityPath right`, the cup generator right-whisker `η ▷ L` replaced by the
left-whisker `R ◁ η`, the cap generator left-whisker `L ◁ ε` by the right-whisker `ε ▷ R`, and
`leftSnakeDoubleWhiskerCollapses` by the shipped `rightSnakeDoubleWhiskerCollapses` (the RIGHT triangle under the
arbitrary double-whisker context).  The mode endpoints swap `base ↔ tip` at the shared leg (B pivots on the right
leg `R : tip ⟶ base`).

  * `sharedLegCupLegB = leftContext ◁ (rightContext ▷ (R ◁ η))` — the cup `η`, LEFT-whiskered by the shared `R`,
    right-whiskered by `rightContext`, left-whiskered by `leftContext`.
  * `sharedLegCapLegB = leftContext ◁ (rightContext ▷ (ε ▷ R))` — the cap `ε`, RIGHT-whiskered by the shared `R`,
    right-whiskered by `rightContext`, left-whiskered by `leftContext`.

and `cupLegB ⊟ capLegB ≈ id` on the shared boundary `leftContext · R · rightContext` — cast-free (the two B legs
compose on the nose exactly as the A legs do).

## What this does NOT close (gates stay `false`)

This is the RIGHT-snake general-context collapse ONLY — the co/op mirror of Gap 2b.  It does NOT specialize to a
concrete `atomFrame cupAtom` / `atomFrame capAtom` (piece i), NOR the delete-chain surgery, NOR the readback
`stepConv`.  No gate flag flips; `convOfMapEq` and the fib-3 gate flags stay `false`.  This brick reads NO
`matchingOf` / `partnerIndexOf` / arc structure — it is pure frame-whisker over the shipped
`SaturatedTwoCellConv` / `rightSnakeDoubleWhiskerCollapses`.

Raw Lean 4 + Init; every proof is the shipped whisker functoriality + the two `whiskerVcomp` distributions +
`rightSnakeDoubleWhiskerCollapses`; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

section GeneralFrameCollapseB

variable {leftSourceMode rightTargetMode : AdjunctionMode}
  (leftContext : ModalityPath adjunctionGraph leftSourceMode AdjunctionMode.tip)
  (rightContext : ModalityPath adjunctionGraph AdjunctionMode.base rightTargetMode)

/-! ## The two shared-leg legs (RIGHT-snake, iterated-whisker presentation, cast-free composable) -/

/-- The cup leg (handedness B): the unit `η` LEFT-whiskered by the shared leg `R`, then right-whiskered by
`rightContext`, then left-whiskered by `leftContext` — the iterated-whisker readback of a cup atom in a RIGHT-snake
shared-leg partner. -/
def sharedLegCupLegB :
    RawTwoCellExpr adjunctionModeSignature
      (composePath leftContext
        (composePath (singletonModalityPath AdjunctionModality.right) rightContext))
      (composePath leftContext
        (composePath (composePath (singletonModalityPath AdjunctionModality.right)
          adjunctionLeftThenRight) rightContext)) :=
  RawTwoCellExpr.whiskerLeft leftContext
    (RawTwoCellExpr.whiskerRight rightContext
      (RawTwoCellExpr.whiskerLeft (singletonModalityPath AdjunctionModality.right)
        adjunctionUnitTwoCell))

/-- The cap leg (handedness B): the counit `ε` RIGHT-whiskered by the shared leg `R`, then right-whiskered by
`rightContext`, then left-whiskered by `leftContext` — the iterated-whisker readback of a cap atom in a RIGHT-snake
shared-leg partner. -/
def sharedLegCapLegB :
    RawTwoCellExpr adjunctionModeSignature
      (composePath leftContext
        (composePath (composePath adjunctionRightThenLeft
          (singletonModalityPath AdjunctionModality.right)) rightContext))
      (composePath leftContext
        (composePath (singletonModalityPath AdjunctionModality.right) rightContext)) :=
  RawTwoCellExpr.whiskerLeft leftContext
    (RawTwoCellExpr.whiskerRight rightContext
      (RawTwoCellExpr.whiskerRight (singletonModalityPath AdjunctionModality.right)
        adjunctionCounitTwoCell))

/-! ## The RIGHT seed snake's two generator legs (named, so the shared middle reduces without metavars) -/

/-- The cup generator leg of the seed RIGHT snake — `R ◁ η`.  Named as a standalone concrete cell so the seed
snake's shared middle `composePath R (L·R) = composePath (R·L) R` reduces on the nose during elaboration. -/
def seedSnakeCupGenLegB :
    RawTwoCellExpr adjunctionModeSignature
      (composePath (singletonModalityPath AdjunctionModality.right)
        (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base))
      (composePath (singletonModalityPath AdjunctionModality.right) adjunctionLeftThenRight) :=
  RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
    (singletonModalityPath AdjunctionModality.right) adjunctionUnitTwoCell

/-- The cap generator leg of the seed RIGHT snake — `ε ▷ R`.  Its source 1-cell `(R·L)·R` is restated in the
`R·(L·R)` bracketing (defeq — both are the word `R L R`) so that it is SYNTACTICALLY the cup leg's target, making
`vcomp seedSnakeCupGenLegB seedSnakeCapGenLegB` compose by `rfl` with no def unfolding. -/
def seedSnakeCapGenLegB :
    RawTwoCellExpr adjunctionModeSignature
      (composePath (singletonModalityPath AdjunctionModality.right) adjunctionLeftThenRight)
      (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)
        (singletonModalityPath AdjunctionModality.right)) :=
  RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
    (singletonModalityPath AdjunctionModality.right) adjunctionCounitTwoCell

/-! ## The distribution: the whiskered RIGHT seed snake IS the two legs' vcomp -/

/-- The whiskered seed RIGHT snake `leftContext ◁ (rightContext ▷ adjunctionSeedRightSnake)` distributes (by the two
`whiskerVcomp` laws) into the vertical composite of the cup and cap legs.  Pure structural convertibility — the
snake's two legs are exactly the cup's and cap's, pulled out of the shared band. -/
theorem whiskeredSnakeDistributesToLegsB :
    TwoCellConvFull adjunctionModeSignature
      (RawTwoCellExpr.whiskerLeft leftContext
        (RawTwoCellExpr.whiskerRight rightContext adjunctionSeedRightSnake))
      (RawTwoCellExpr.vcomp (sharedLegCupLegB leftContext rightContext)
        (sharedLegCapLegB leftContext rightContext)) := by
  show TwoCellConvFull adjunctionModeSignature
      (RawTwoCellExpr.whiskerLeft leftContext
        (RawTwoCellExpr.whiskerRight rightContext
          (RawTwoCellExpr.vcomp seedSnakeCupGenLegB seedSnakeCapGenLegB)))
      (RawTwoCellExpr.vcomp (sharedLegCupLegB leftContext rightContext)
        (sharedLegCapLegB leftContext rightContext))
  exact TwoCellConvFull.trans
    (TwoCellConvFull.whiskerLeftCongr leftContext
      (TwoCellConvFull.ofConv (TwoCellConv.ofStep
        (TwoCellStep.whiskerRightVcomp rightContext seedSnakeCupGenLegB seedSnakeCapGenLegB))))
    (TwoCellConvFull.ofConv (TwoCellConv.ofStep (TwoCellStep.whiskerLeftVcomp leftContext
      (RawTwoCellExpr.whiskerRight rightContext seedSnakeCupGenLegB)
      (RawTwoCellExpr.whiskerRight rightContext seedSnakeCapGenLegB))))

/-! ## Handedness B — the GENERAL shared-leg frame collapse (cast-free) -/

/-- ★★ **Handedness B (RIGHT snake), CLOSED (cast-free).**  For ARBITRARY whisker words `leftContext` /
`rightContext`, the RIGHT-snake shared-leg cup and cap legs compose to the identity on the shared boundary
`leftContext · R · rightContext`: `cupLegB ⊟ capLegB ≈ id`.  Proof: the vcomp re-folds (by
`whiskeredSnakeDistributesToLegsB`, reversed) into the whiskered seed RIGHT snake `leftContext ◁ (rightContext ▷
adjunctionSeedRightSnake)`, which collapses to the identity by the shipped `rightSnakeDoubleWhiskerCollapses` (the
RIGHT triangle under the arbitrary double-whisker context).  The two legs compose CAST-FREE (their shared middle is
definitionally common).  This is the co/op mirror of `generalContextFrameLegsCollapse`, the mate of the LEFT
triangle (Kelly–Street / RV Prop 3.3.4 "dual argument"), re-proven — not transported. -/
theorem generalContextFrameLegsCollapseB :
    SaturatedTwoCellConv
      (RawTwoCellExpr.vcomp (sharedLegCupLegB leftContext rightContext)
        (sharedLegCapLegB leftContext rightContext))
      (RawTwoCellExpr.id (signature := adjunctionModeSignature)
        (composePath leftContext
          (composePath (singletonModalityPath AdjunctionModality.right) rightContext))) :=
  SaturatedTwoCellConv.trans
    (SaturatedTwoCellConv.ofFull
      (TwoCellConvFull.symm (whiskeredSnakeDistributesToLegsB leftContext rightContext)))
    (rightSnakeDoubleWhiskerCollapses leftContext rightContext)

/-! ## Feeding `snakeStraightensInContext` — the handedness-B collapse discharges its hypothesis -/

/-- ★ **The general RIGHT-snake shared-leg partner straightens in arbitrary vertical context** — the cast-free
handedness-B collapse `generalContextFrameLegsCollapseB` supplied as the `collapses` hypothesis of the shipped
`snakeStraightensInContext`. -/
theorem generalContextSnakeStraightensInContextB
    {pathPre pathHigh : ModalityPath adjunctionGraph leftSourceMode rightTargetMode}
    (pre : RawTwoCellExpr adjunctionModeSignature pathPre
      (composePath leftContext
        (composePath (singletonModalityPath AdjunctionModality.right) rightContext)))
    (tail : RawTwoCellExpr adjunctionModeSignature
      (composePath leftContext
        (composePath (singletonModalityPath AdjunctionModality.right) rightContext))
      pathHigh) :
    SaturatedTwoCellConv
      (RawTwoCellExpr.vcomp pre
        (RawTwoCellExpr.vcomp (sharedLegCupLegB leftContext rightContext)
          (RawTwoCellExpr.vcomp (sharedLegCapLegB leftContext rightContext) tail)))
      (RawTwoCellExpr.vcomp pre tail) :=
  snakeStraightensInContext pre (sharedLegCupLegB leftContext rightContext)
    (sharedLegCapLegB leftContext rightContext)
    (generalContextFrameLegsCollapseB leftContext rightContext) tail

end GeneralFrameCollapseB

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the HANDEDNESS-B (RIGHT-snake) general shared-leg frame collapse is DISCHARGED, cast-free.**
`generalContextFrameLegsCollapseB` proves `cupLegB ⊟ capLegB ≈ id` for ARBITRARY composite whisker words under the
RIGHT-snake shared-leg geometry, in the iterated-whisker leg presentation that composes on the nose — no boundary
cast.  It re-folds the two legs into the whiskered seed RIGHT snake (`whiskeredSnakeDistributesToLegsB`) and fires
the shipped triangle collapse (`rightSnakeDoubleWhiskerCollapses`).  This is the co/op mirror of the shipped
handedness-A `generalContextFrameLegsCollapse` — the mate of the LEFT triangle under the Kelly–Street mate
involution (RV Prop 3.3.4's "dual argument"), RE-PROVEN by the mechanical clone (there is no dagger functor to
transport it for free).  Handedness B is genuinely reachable (`zigZagSharedLeg_widthDichotomy` is `A ∨ B`), so this
collapse is MANDATORY for the STRAIGHTEN producer's totality, not a convenience.

  What this marker does NOT claim (gates stay `false`): the atom-INSTANCE specialization (piece i), the
  delete-chain surgery, and the readback `stepConv`.  `convOfMapEq` and the fib-3 gate flags stay `false`.
  `= true`. -/
def fxMode_hasGeneralSharedLegFrameCollapseB : Bool := true

end FX1Poly.Polygraph
