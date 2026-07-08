import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyCellLift
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.WhiskerReframing

/-! # mode-3 keystone — Piece I STRAIGHTEN Gap 2b: the GENERAL shared-leg frame collapse

`SpineValleyCellLift` shipped `snakePrefixStraightens` / `snakeStraightensInContext`: a partner cup·cap pair whose
two per-atom frames `cupFrame ⊟ capFrame` collapse to the identity STRAIGHTENS at the head of a readback chain and
in any surrounding vertical context.  Those consume the collapse `cupFrame ⊟ capFrame ≈ id` as a HYPOTHESIS.

`MonotoneFaithful` shipped that collapse only at BLOCK POSITION 0 (`staircaseSnakeAtZeroCollapses`) and, by
whiskering the whole position-0 vcomp on the left by the canonical word `(L·R)^leftBlocks`, at any block position
for the CANONICAL staircase atoms (`staircaseSnakeWhiskeredCollapses`).  What was open (Gap 2b): the collapse for
a partner pair whose per-atom frames carry ARBITRARY composite whisker contexts, under the shared-leg matched-arc
geometry.

★ **This file discharges Gap 2b.**  Fix the shared leg `L = singletonModalityPath left` and ARBITRARY whisker
words `leftContext` (left band) and `rightContext` (right band).  A genuine non-crossing cup·cap partner reads
back as the two shared-leg legs

  * `cupLeg = leftContext ◁ (rightContext ▷ (L ▷ η))`      (the cup `η`, right-whiskered by the shared `L` then by `rightContext`, left-whiskered by `leftContext`)
  * `capLeg = leftContext ◁ (rightContext ▷ (L ◁ ε))`      (the cap `ε`, left-whiskered by the shared `L`, right-whiskered by `rightContext`, left-whiskered by `leftContext`)

and `cupLeg ⊟ capLeg ≈ id` on the shared boundary `leftContext · L · rightContext` — the general-context frame
collapse, CAST-FREE.  These two legs compose on the NOSE (their shared middle `leftContext · (L·R) · L ·
rightContext` is definitionally common), so no boundary cast is needed to even state the vcomp — the collapse
`generalContextFrameLegsCollapse` is unconditional and directly discharges the `collapses` hypothesis of
`snakeStraightensInContext` (see `generalContextSnakeStraightensInContext`).

## The re-bracketing chain (all shipped lemmas, no new primitive)

`cupLeg ⊟ capLeg` re-folds onto the whiskered seed snake `leftContext ◁ (rightContext ▷ adjunctionSeedLeftSnake)`
by the two distribution laws `whiskerLeftVcomp` / `whiskerRightVcomp` (the snake's two legs ARE the cup and cap
legs, distributed out of the shared band), and that whiskered snake collapses to the identity by the shipped
`leftSnakeDoubleWhiskerCollapses` (the TRIANGLE fired under the arbitrary double-whisker context).  The
disjoint-whisker exchange `whiskerExchange` used here is the UNCONDITIONAL strict-2-category coherence (a
constructor of `SaturatedTwoCellConv` / `TwoCellConvFull`, not a conditional interchange), so the collapse is
true for EVERY `leftContext` / `rightContext` — there is no hidden-false whisker configuration.

## The merged-`atomFrame` presentation and its honest boundary cast

The readback's `atomFrame` presents each atom's whisker context MERGED into a single left/right whisker:
`cupFrame = leftContext ◁ ((L · rightContext) ▷ η)` and `capFrame = (leftContext · L) ◁ (rightContext ▷ ε)`.  The
iterated legs above are `TwoCellConvFull` to these merged frames by pure whisker functoriality
(`cupLegSplitsToMergedCupFrameInner` / `capLegSplitsToMergedCapFrameInner` exhibit the per-atom split via the
shipped `whiskerRightComp` / `whiskerExchange`).  But for a VARIABLE `leftContext` the merged frames' shared middle
`leftContext · (L·R) · (L · rightContext)` (cup target) versus `(leftContext · L) · (R·L) · rightContext` (cap
source) are only PROPOSITIONALLY equal — the same word up to the `composePath`-associativity of the `leftContext ·
L` prefix — so the literal `vcomp cupFrame capFrame` in the merged presentation does NOT typecheck without a
boundary cast (at position 0, `leftContext = nil`, the prefix reduces and the cast vanishes, recovering
`staircaseSnakeAtZeroCollapses`).  That associativity cast is precisely the inter-atom boundary-coherence datum
the SEPARATE 2a realization (the matched-arc partner witness) supplies; the CAST-FREE iterated-leg collapse above
sidesteps it, which is why it is the clean Gap-2b closer.

## What this does NOT close (gates stay `false`)

This is Gap 2b ONLY — the frame-whisker re-bracketing, given the shared-leg geometry as the SHAPE of the legs.
STRAIGHTEN still owes the 2a partner witness: proving an adjacent cup·cap redex in a valley is a genuine
non-crossing partner whose readback HAS this shared-leg shape (partner-discrimination + the realized-chain
coherence).  No gate flag flips; `convOfMapEq` and the fib-3 gate flags stay `false`.  This brick imports no
spine-to-boundary arc-readoff (the dead route) — it is pure frame-whisker over the shipped `SaturatedTwoCellConv`.

Raw Lean 4 + Init; every proof is the shipped whisker functoriality + the two `whiskerVcomp` distributions +
`leftSnakeDoubleWhiskerCollapses`; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

section GeneralFrameCollapse

variable {leftSourceMode rightTargetMode : AdjunctionMode}
  (leftContext : ModalityPath adjunctionGraph leftSourceMode AdjunctionMode.base)
  (rightContext : ModalityPath adjunctionGraph AdjunctionMode.tip rightTargetMode)

/-! ## The two shared-leg legs (iterated-whisker presentation, cast-free composable) -/

/-- The cup leg: the unit `η` whiskered by the shared leg `L` (right), then by `rightContext` (right), then by
`leftContext` (left) — the iterated-whisker readback of a cup atom in a shared-leg partner. -/
def sharedLegCupLeg :
    RawTwoCellExpr adjunctionModeSignature
      (composePath leftContext
        (composePath (singletonModalityPath AdjunctionModality.left) rightContext))
      (composePath leftContext
        (composePath (composePath adjunctionLeftThenRight
          (singletonModalityPath AdjunctionModality.left)) rightContext)) :=
  RawTwoCellExpr.whiskerLeft leftContext
    (RawTwoCellExpr.whiskerRight rightContext
      (RawTwoCellExpr.whiskerRight (singletonModalityPath AdjunctionModality.left)
        adjunctionUnitTwoCell))

/-- The cap leg: the counit `ε` whiskered by the shared leg `L` (left), then by `rightContext` (right), then by
`leftContext` (left) — the iterated-whisker readback of a cap atom in a shared-leg partner. -/
def sharedLegCapLeg :
    RawTwoCellExpr adjunctionModeSignature
      (composePath leftContext
        (composePath (composePath (singletonModalityPath AdjunctionModality.left)
          adjunctionRightThenLeft) rightContext))
      (composePath leftContext
        (composePath (singletonModalityPath AdjunctionModality.left) rightContext)) :=
  RawTwoCellExpr.whiskerLeft leftContext
    (RawTwoCellExpr.whiskerRight rightContext
      (RawTwoCellExpr.whiskerLeft (singletonModalityPath AdjunctionModality.left)
        adjunctionCounitTwoCell))

/-! ## The seed snake's two generator legs (named, so the shared middle reduces without metavars) -/

/-- The cup generator leg of the seed left snake — `η ▷ L`.  Named as a standalone concrete cell so the seed
snake's shared middle `composePath (L·R) L = composePath L (R·L)` reduces on the nose during elaboration
(the metavar-floated vcomp of the two whiskers does not). -/
def seedSnakeCupGenLeg :
    RawTwoCellExpr adjunctionModeSignature
      (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
        (singletonModalityPath AdjunctionModality.left))
      (composePath adjunctionLeftThenRight (singletonModalityPath AdjunctionModality.left)) :=
  RawTwoCellExpr.whiskerRight (signature := adjunctionModeSignature)
    (singletonModalityPath AdjunctionModality.left) adjunctionUnitTwoCell

/-- The cap generator leg of the seed left snake — `L ◁ ε`.  Its source 1-cell `L · (R·L)` is restated in the
`(L·R) · L` bracketing (defeq — both are the word `L R L`) so that it is SYNTACTICALLY the cup leg's target, making
`vcomp seedSnakeCupGenLeg seedSnakeCapGenLeg` (and its right-whiskering) compose by `rfl` with no def unfolding. -/
def seedSnakeCapGenLeg :
    RawTwoCellExpr adjunctionModeSignature
      (composePath adjunctionLeftThenRight (singletonModalityPath AdjunctionModality.left))
      (composePath (singletonModalityPath AdjunctionModality.left)
        (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip)) :=
  RawTwoCellExpr.whiskerLeft (signature := adjunctionModeSignature)
    (singletonModalityPath AdjunctionModality.left) adjunctionCounitTwoCell

/-! ## The distribution: the whiskered seed snake IS the two legs' vcomp -/

/-- The whiskered seed left snake `leftContext ◁ (rightContext ▷ adjunctionSeedLeftSnake)` distributes (by the two
`whiskerVcomp` laws) into the vertical composite of the cup and cap legs.  Pure structural convertibility — the
snake's two legs are exactly the cup's and cap's, pulled out of the shared band. -/
theorem whiskeredSnakeDistributesToLegs :
    TwoCellConvFull adjunctionModeSignature
      (RawTwoCellExpr.whiskerLeft leftContext
        (RawTwoCellExpr.whiskerRight rightContext adjunctionSeedLeftSnake))
      (RawTwoCellExpr.vcomp (sharedLegCupLeg leftContext rightContext)
        (sharedLegCapLeg leftContext rightContext)) := by
  show TwoCellConvFull adjunctionModeSignature
      (RawTwoCellExpr.whiskerLeft leftContext
        (RawTwoCellExpr.whiskerRight rightContext
          (RawTwoCellExpr.vcomp seedSnakeCupGenLeg seedSnakeCapGenLeg)))
      (RawTwoCellExpr.vcomp (sharedLegCupLeg leftContext rightContext)
        (sharedLegCapLeg leftContext rightContext))
  exact TwoCellConvFull.trans
    (TwoCellConvFull.whiskerLeftCongr leftContext
      (TwoCellConvFull.ofConv (TwoCellConv.ofStep
        (TwoCellStep.whiskerRightVcomp rightContext seedSnakeCupGenLeg seedSnakeCapGenLeg))))
    (TwoCellConvFull.ofConv (TwoCellConv.ofStep (TwoCellStep.whiskerLeftVcomp leftContext
      (RawTwoCellExpr.whiskerRight rightContext seedSnakeCupGenLeg)
      (RawTwoCellExpr.whiskerRight rightContext seedSnakeCapGenLeg))))

/-! ## Gap 2b — the GENERAL shared-leg frame collapse (cast-free) -/

/-- ★★ **Gap 2b, CLOSED (cast-free).**  For ARBITRARY whisker words `leftContext` / `rightContext`, the shared-leg
cup and cap legs compose to the identity on the shared boundary `leftContext · L · rightContext`:
`cupLeg ⊟ capLeg ≈ id`.  Proof: the vcomp re-folds (by `whiskeredSnakeDistributesToLegs`, reversed) into the
whiskered seed snake `leftContext ◁ (rightContext ▷ adjunctionSeedLeftSnake)`, which collapses to the identity by
the shipped `leftSnakeDoubleWhiskerCollapses` (the TRIANGLE under the arbitrary double-whisker context).  The two
legs compose CAST-FREE (their shared middle is definitionally common), so no boundary cast enters the statement —
this is the clean general-context refutation of any "arbitrary-context wall": there is no hidden-false whisker
configuration, `whiskerExchange` being the unconditional strict-2-category coherence. -/
theorem generalContextFrameLegsCollapse :
    SaturatedTwoCellConv
      (RawTwoCellExpr.vcomp (sharedLegCupLeg leftContext rightContext)
        (sharedLegCapLeg leftContext rightContext))
      (RawTwoCellExpr.id (signature := adjunctionModeSignature)
        (composePath leftContext
          (composePath (singletonModalityPath AdjunctionModality.left) rightContext))) :=
  SaturatedTwoCellConv.trans
    (SaturatedTwoCellConv.ofFull
      (TwoCellConvFull.symm (whiskeredSnakeDistributesToLegs leftContext rightContext)))
    (leftSnakeDoubleWhiskerCollapses leftContext rightContext)

/-! ## Feeding `snakeStraightensInContext` — the collapse discharges its hypothesis -/

/-- ★ **The general shared-leg partner straightens in arbitrary vertical context** — the cast-free general frame
collapse `generalContextFrameLegsCollapse` supplied as the `collapses` hypothesis of the shipped
`snakeStraightensInContext`.  So a shared-leg cup·cap redex at ANY whisker context, located at depth in a readback
chain, straightens away: `pre ⊟ (cupLeg ⊟ (capLeg ⊟ tail)) ≈ pre ⊟ tail`.  This is the exact currency the Piece I
STRAIGHTEN descent step consumes for a matched (shared-leg) partner pair. -/
theorem generalContextSnakeStraightensInContext
    {pathPre pathHigh : ModalityPath adjunctionGraph leftSourceMode rightTargetMode}
    (pre : RawTwoCellExpr adjunctionModeSignature pathPre
      (composePath leftContext
        (composePath (singletonModalityPath AdjunctionModality.left) rightContext)))
    (tail : RawTwoCellExpr adjunctionModeSignature
      (composePath leftContext
        (composePath (singletonModalityPath AdjunctionModality.left) rightContext))
      pathHigh) :
    SaturatedTwoCellConv
      (RawTwoCellExpr.vcomp pre
        (RawTwoCellExpr.vcomp (sharedLegCupLeg leftContext rightContext)
          (RawTwoCellExpr.vcomp (sharedLegCapLeg leftContext rightContext) tail)))
      (RawTwoCellExpr.vcomp pre tail) :=
  snakeStraightensInContext pre (sharedLegCupLeg leftContext rightContext)
    (sharedLegCapLeg leftContext rightContext)
    (generalContextFrameLegsCollapse leftContext rightContext) tail

/-! ## The merged-`atomFrame` presentation — the legs ARE the atom frames, up to whisker functoriality -/

/-- The cup leg's inner (before the outer `leftContext ◁ -`) is the merged cup `atomFrame` inner
`(L · rightContext) ▷ η` up to a `composePath`-associativity boundary cast — the shipped `whiskerRightComp`
read as: the merged single right-whisker by `L · rightContext` splits into the iterated `rightContext ▷ (L ▷ η)`.
This exhibits the iterated cup leg as the merged cup frame modulo whisker functoriality. -/
theorem cupLegSplitsToMergedCupFrameInner :
    TwoCellConvFull adjunctionModeSignature
      (RawTwoCellExpr.whiskerRight
        (composePath (singletonModalityPath AdjunctionModality.left) rightContext)
        adjunctionUnitTwoCell)
      (RawTwoCellExpr.castBoundary
        (composePath_assoc (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
          (singletonModalityPath AdjunctionModality.left) rightContext)
        (composePath_assoc adjunctionLeftThenRight
          (singletonModalityPath AdjunctionModality.left) rightContext)
        (RawTwoCellExpr.whiskerRight rightContext
          (RawTwoCellExpr.whiskerRight (singletonModalityPath AdjunctionModality.left)
            adjunctionUnitTwoCell))) :=
  TwoCellConvFull.whiskerRightComp (singletonModalityPath AdjunctionModality.left) rightContext
    adjunctionUnitTwoCell

/-- The cap leg's inner `rightContext ▷ (L ◁ ε)` is the merged cap `atomFrame` inner `L ◁ (rightContext ▷ ε)` up
to a `composePath`-associativity boundary cast — the shipped `whiskerExchange` (the unconditional disjoint-whisker
commute) at `leftWhisker = L`, `rightWhisker = rightContext`, `body = ε`.  This exhibits the iterated cap leg as
the merged cap frame modulo the strict-2-category exchange coherence. -/
theorem capLegSplitsToMergedCapFrameInner :
    TwoCellConvFull adjunctionModeSignature
      (RawTwoCellExpr.whiskerLeft (singletonModalityPath AdjunctionModality.left)
        (RawTwoCellExpr.whiskerRight rightContext adjunctionCounitTwoCell))
      (RawTwoCellExpr.castBoundary
        (composePath_assoc (singletonModalityPath AdjunctionModality.left)
          adjunctionRightThenLeft rightContext)
        (composePath_assoc (singletonModalityPath AdjunctionModality.left)
          (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip) rightContext)
        (RawTwoCellExpr.whiskerRight rightContext
          (RawTwoCellExpr.whiskerLeft (singletonModalityPath AdjunctionModality.left)
            adjunctionCounitTwoCell))) :=
  TwoCellConvFull.whiskerExchange (singletonModalityPath AdjunctionModality.left) rightContext
    adjunctionCounitTwoCell

end GeneralFrameCollapse

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — Gap 2b (the general shared-leg frame collapse) is DISCHARGED, cast-free.**
`generalContextFrameLegsCollapse` proves `cupLeg ⊟ capLeg ≈ id` for ARBITRARY composite whisker words
`leftContext` / `rightContext` under the shared-leg geometry, in the iterated-whisker leg presentation that
composes on the nose — no boundary cast in the statement.  It re-folds the two legs into the whiskered seed snake
(`whiskeredSnakeDistributesToLegs`) and fires the shipped triangle collapse
(`leftSnakeDoubleWhiskerCollapses`).  The disjoint-whisker exchange it rests on is the UNCONDITIONAL
strict-2-category coherence, so there is NO hidden-false whisker configuration — the general collapse is true for
every context.  It feeds `snakeStraightensInContext` directly (`generalContextSnakeStraightensInContext`).  The
merged-`atomFrame` presentation differs from the iterated legs by a pure `composePath`-associativity boundary cast
(`cupLegSplitsToMergedCupFrameInner` / `capLegSplitsToMergedCapFrameInner` exhibit the per-atom split); that cast
is the inter-atom boundary-coherence datum the SEPARATE 2a realization supplies, not this brick's concern.

  What this marker does NOT claim (gates stay `false`): the 2a partner witness — that an adjacent cup·cap redex in
  a valley is a genuine non-crossing partner whose readback HAS the shared-leg leg shape (partner-discrimination +
  realized-chain coherence).  STRAIGHTEN is reduced to that 2a witness ALONE; `convOfMapEq` and the fib-3 gate
  flags stay `false`.  `= true`. -/
def fxMode_hasGeneralSharedLegFrameCollapse : Bool := true

end FX1Poly.Polygraph
