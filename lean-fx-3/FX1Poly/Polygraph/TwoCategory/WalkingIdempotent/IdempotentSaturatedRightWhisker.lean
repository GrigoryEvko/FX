import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentSaturatedGeneralBricks

/-! # WalkingIdempotent/IdempotentSaturatedRightWhisker — the grow-half right-whisker, GENERIC-NATIVE

The GROW-half right-whisker (`growTowerRightWhiskerGen`) and the general-width `whiskerRightCanonGen`, re-founded
DIRECTLY over `SaturatedConvOver monadModeSignature IdempotentLawRel`.  Mirrors `IdempotentMonadRightWhisker`
arm-for-arm.  The conv-FREE `whiskerRight_whiskerEq` and the `t`-power boundary lemmas are REUSED from the bespoke
lane; the relation-generic cast helpers are re-proved here at the generic carrier.

Raw Lean 4 + Init; STRUCTURAL `Nat` recursion; every proof BUILDS conv values.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration `#assert_no_axioms` gated
in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph
open SaturatedConvOver

/-! ## Signature-generic cast-manipulation helpers (CONV-level, applied) -/

/-- Boundary-cast fusion (CONV form), generic-native.  Mirrors `castChainCollapseConv`. -/
theorem castChainCollapseConvGen
    {sourcePath sourcePath' sourcePath'' targetPath targetPath' targetPath'' :
      ModalityPath monadGraph MonadMode.point MonadMode.point}
    (hsourceFirst : sourcePath = sourcePath') (htargetFirst : targetPath = targetPath')
    (hsourceSecond : sourcePath' = sourcePath'') (htargetSecond : targetPath' = targetPath'')
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    SaturatedConvOver monadModeSignature IdempotentLawRel
      (RawTwoCellExpr.castBoundary hsourceSecond htargetSecond
        (RawTwoCellExpr.castBoundary hsourceFirst htargetFirst cell))
      (RawTwoCellExpr.castBoundary (hsourceFirst.trans hsourceSecond) (htargetFirst.trans htargetSecond) cell) := by
  cases hsourceFirst; cases htargetFirst; cases hsourceSecond; cases htargetSecond
  exact SaturatedConvOver.refl _

/-- Extrude a boundary cast out of a `monadT` RIGHT-whisker (CONV form), generic-native.  Mirrors
`whiskerRightPullMonadTConv`. -/
theorem whiskerRightPullMonadTConvGen
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath monadGraph MonadMode.point MonadMode.point}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    SaturatedConvOver monadModeSignature IdempotentLawRel
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT
        (RawTwoCellExpr.castBoundary hsource htarget cell))
      (RawTwoCellExpr.castBoundary (congrArg (fun path => composePath path monadT) hsource)
        (congrArg (fun path => composePath path monadT) htarget)
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT cell)) := by
  cases hsource; cases htarget
  exact SaturatedConvOver.refl _

/-- Merge two casts across a vertical composite (CONV form), generic-native.  Mirrors `vcompCastMergeConv`. -/
theorem vcompCastMergeConvGen
    {sourcePath sourcePath' middlePath middlePath' targetPath targetPath' :
      ModalityPath monadGraph MonadMode.point MonadMode.point}
    (hsource : sourcePath = sourcePath') (hmiddle : middlePath = middlePath') (htarget : targetPath = targetPath')
    (cellAlpha : RawTwoCellExpr monadModeSignature sourcePath middlePath)
    (cellBeta : RawTwoCellExpr monadModeSignature middlePath targetPath) :
    SaturatedConvOver monadModeSignature IdempotentLawRel
      (RawTwoCellExpr.vcomp (RawTwoCellExpr.castBoundary hsource hmiddle cellAlpha)
        (RawTwoCellExpr.castBoundary hmiddle htarget cellBeta))
      (RawTwoCellExpr.castBoundary hsource htarget (RawTwoCellExpr.vcomp cellAlpha cellBeta)) := by
  cases hsource; cases hmiddle; cases htarget
  exact SaturatedConvOver.refl _

/-! ## Right-section cancellation (the idempotence carrier for the grow-half) -/

/-- **Right-section cancellation**, generic-native.  Mirrors `idempotentRightSectionCancel`. -/
theorem idempotentRightSectionCancelGen
    {oneCellP oneCellQ : ModalityPath monadGraph MonadMode.point MonadMode.point}
    (foldMap : RawTwoCellExpr monadModeSignature oneCellQ oneCellP)
    (growMap : RawTwoCellExpr monadModeSignature oneCellP oneCellQ)
    (hfg : SaturatedConvOver monadModeSignature IdempotentLawRel (RawTwoCellExpr.vcomp foldMap growMap)
      (RawTwoCellExpr.id (signature := monadModeSignature) oneCellQ))
    {cellA cellB : RawTwoCellExpr monadModeSignature oneCellP oneCellQ}
    (hAB : SaturatedConvOver monadModeSignature IdempotentLawRel (RawTwoCellExpr.vcomp cellA foldMap)
      (RawTwoCellExpr.vcomp cellB foldMap)) :
    SaturatedConvOver monadModeSignature IdempotentLawRel cellA cellB := by
  refine SaturatedConvOver.trans (SaturatedConvOver.symm (idemStep (TwoCellStep.vcompIdRight cellA))) ?_
  refine SaturatedConvOver.trans (vcompCongrRight cellA (SaturatedConvOver.symm hfg)) ?_
  refine SaturatedConvOver.trans (SaturatedConvOver.symm (idemStep (TwoCellStep.vcompAssoc cellA foldMap growMap))) ?_
  refine SaturatedConvOver.trans (vcompCongrLeft growMap hAB) ?_
  refine SaturatedConvOver.trans (idemStep (TwoCellStep.vcompAssoc cellB foldMap growMap)) ?_
  refine SaturatedConvOver.trans (vcompCongrRight cellB hfg) ?_
  exact idemStep (TwoCellStep.vcompIdRight cellB)

/-! ## The grow-then-fold column collapse -/

/-- ★ **Grow-column-fold ~ mu**, generic-native.  Mirrors `growColumnFold`. -/
theorem growColumnFoldGen (n : Nat) :
    SaturatedConvOver monadModeSignature IdempotentLawRel
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT (growTower n))
        (RawTwoCellExpr.castBoundary (composePath_monadTPower_monadT (n + 1)).symm rfl
          (monadGadget (n + 2))))
      monadMulTwoCell := by
  refine SaturatedConvOver.trans (vcompCongrRight _ (SaturatedConvOver.symm (gadgetSplitRightGen (n + 1)))) ?_
  refine SaturatedConvOver.trans (SaturatedConvOver.symm (idemStep (TwoCellStep.vcompAssoc
    (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT (growTower n))
    (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT (monadGadget (n + 1)))
    monadMulTwoCell))) ?_
  refine SaturatedConvOver.trans (vcompCongrLeft monadMulTwoCell (SaturatedConvOver.symm (idemStep
    (TwoCellStep.whiskerRightVcomp monadT (growTower n) (monadGadget (n + 1)))))) ?_
  refine SaturatedConvOver.trans (vcompCongrLeft monadMulTwoCell (whiskerRightCongr monadT (growThenFoldGen n))) ?_
  refine SaturatedConvOver.trans (vcompCongrLeft monadMulTwoCell (idemStep
    (TwoCellStep.whiskerRightId (signature := monadModeSignature) monadT monadT))) ?_
  exact idemStep (TwoCellStep.vcompIdLeft monadMulTwoCell)

/-! ## The grow-half right-whisker -/

/-- ★★ **The GROW-half right-whisker**, generic-native.  Mirrors `growTowerRightWhisker`. -/
theorem growTowerRightWhiskerGen (n : Nat) :
    SaturatedConvOver monadModeSignature IdempotentLawRel
      (RawTwoCellExpr.castBoundary rfl (composePath_monadTPower_monadT (n + 1))
        (RawTwoCellExpr.vcomp monadEtaTCell
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT (growTower n))))
      (growTower (n + 1)) := by
  refine idempotentRightSectionCancelGen (monadGadget (n + 2)) (growTower (n + 1)) (foldThenGrowGen (n + 1)) ?_
  refine SaturatedConvOver.trans ?_ (SaturatedConvOver.symm (growThenFoldGen (n + 1)))
  refine SaturatedConvOver.trans (vcompCastLeftExtrudeGen rfl (composePath_monadTPower_monadT (n + 1))
    (RawTwoCellExpr.vcomp monadEtaTCell
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT (growTower n)))
    (monadGadget (n + 2))) ?_
  show SaturatedConvOver monadModeSignature IdempotentLawRel
    (RawTwoCellExpr.vcomp
      (RawTwoCellExpr.vcomp monadEtaTCell
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT (growTower n)))
      (RawTwoCellExpr.castBoundary (composePath_monadTPower_monadT (n + 1)).symm rfl (monadGadget (n + 2))))
    (RawTwoCellExpr.id (signature := monadModeSignature) monadT)
  refine SaturatedConvOver.trans (idemStep (TwoCellStep.vcompAssoc monadEtaTCell
    (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT (growTower n))
    (RawTwoCellExpr.castBoundary (composePath_monadTPower_monadT (n + 1)).symm rfl
      (monadGadget (n + 2))))) ?_
  refine SaturatedConvOver.trans (vcompCongrRight monadEtaTCell (growColumnFoldGen n)) ?_
  exact idemLeftUnitLaw

/-! ## The single-`t` RIGHT-whisker canonicalisation -/

/-- ★ **Single-`t` RIGHT-whisker canonicalisation**, generic-native.  Mirrors `whiskerRightCanonOne`. -/
theorem whiskerRightCanonOneGen (a n : Nat) :
    SaturatedConvOver monadModeSignature IdempotentLawRel
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT (canonThroughT a n))
      (RawTwoCellExpr.castBoundary (composePath_monadTPower_monadT a).symm
        (composePath_monadTPower_monadT (n + 1)).symm (canonThroughT (a + 1) (n + 1))) := by
  show SaturatedConvOver monadModeSignature IdempotentLawRel
    (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT
      (RawTwoCellExpr.vcomp (monadGadget a) (growTower n))) _
  refine SaturatedConvOver.trans (idemStep
    (TwoCellStep.whiskerRightVcomp monadT (monadGadget a) (growTower n))) ?_
  refine SaturatedConvOver.trans (vcompCongrRight _ (SaturatedConvOver.symm (idemStep
    (TwoCellStep.vcompIdLeft
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT (growTower n)))))) ?_
  refine SaturatedConvOver.trans (vcompCongrRight _ (vcompCongrLeft _ (SaturatedConvOver.symm idempotentMulRightInverse_gen))) ?_
  refine SaturatedConvOver.trans (vcompCongrRight _ (idemStep
    (TwoCellStep.vcompAssoc monadMulTwoCell monadEtaTCell
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT (growTower n))))) ?_
  refine SaturatedConvOver.trans (SaturatedConvOver.symm (idemStep
    (TwoCellStep.vcompAssoc
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT (monadGadget a))
      monadMulTwoCell
      (RawTwoCellExpr.vcomp monadEtaTCell
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT (growTower n)))))) ?_
  refine SaturatedConvOver.trans (vcompCongrLeft _ (gadgetSplitRightGen a)) ?_
  refine SaturatedConvOver.trans (vcompCongrRight _
    (ofCastLeftGen rfl (composePath_monadTPower_monadT (n + 1))
      (growTowerRightWhiskerGen n))) ?_
  exact vcompCastMergeConvGen (composePath_monadTPower_monadT a).symm rfl
    (composePath_monadTPower_monadT (n + 1)).symm (monadGadget (a + 1)) (growTower (n + 1))

/-! ## The general-width RIGHT-whisker canonicalisation -/

/-- ★ **General-width RIGHT-whisker canonicalisation**, generic-native.  Mirrors `whiskerRightCanon`. -/
theorem whiskerRightCanonGen : (k a n : Nat) →
    SaturatedConvOver monadModeSignature IdempotentLawRel
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower k) (canonThroughT a n))
      (RawTwoCellExpr.castBoundary (monadTPower_add a k) (monadTPower_succ_add_right n k)
        (canonThroughT (a + k) (n + k)))
  | 0, a, n => idemFull (TwoCellConvFull.whiskerRightUnit (canonThroughT a n))
  | k + 1, a, n => by
      rw [whiskerRight_whiskerEq (composePath_monadTPower_monadT k) (canonThroughT a n)]
      refine SaturatedConvOver.trans (castBoundaryCongrGen _ _ (idemFull
        (TwoCellConvFull.whiskerRightComp (monadTPower k) monadT (canonThroughT a n)))) ?_
      refine SaturatedConvOver.trans (castChainCollapseConvGen _ _ _ _ _) ?_
      refine SaturatedConvOver.trans (castBoundaryCongrGen _ _ (whiskerRightCongr monadT (whiskerRightCanonGen k a n))) ?_
      refine SaturatedConvOver.trans (castBoundaryCongrGen _ _
        (whiskerRightPullMonadTConvGen _ _ (canonThroughT (a + k) (n + k)))) ?_
      refine SaturatedConvOver.trans (castChainCollapseConvGen _ _ _ _ _) ?_
      refine SaturatedConvOver.trans (castBoundaryCongrGen _ _ (whiskerRightCanonOneGen (a + k) (n + k))) ?_
      refine SaturatedConvOver.trans (castChainCollapseConvGen _ _ _ _ _) ?_
      exact SaturatedConvOver.refl _

end FX1Poly.Polygraph.Amalgam
