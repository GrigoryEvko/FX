import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentSaturatedLadder

/-! # WalkingIdempotent/IdempotentSaturatedGeneralBricks — the general-width bricks, GENERIC-NATIVE

The general-width LEFT-whisker canonicalisation (`whiskerLeftCanonGen`) and the RIGHT-leaning mu-tree peel
(`gadgetSplitRightGen`) re-founded DIRECTLY over `SaturatedConvOver monadModeSignature IdempotentLawRel`.  Mirrors
`IdempotentMonadGeneralNormalizer` arm-for-arm.  The cast/congruence helpers (relation-generic: proved by `cases`
on the boundary equalities) are re-proved here at the generic carrier; the conv-FREE `t`-power boundary lemmas
(`monadTPower_add_left`, `monadTPower_succ_add_left`, `composePath_monadTPower_monadT`, `monadWhiskerLeft_castBoundary`)
are REUSED from the bespoke lane.

Raw Lean 4 + Init; STRUCTURAL recursion; every proof BUILDS conv values.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration `#assert_no_axioms` gated
in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph
open SaturatedConvOver

/-! ## Boundary-cast helpers on the generic saturated relation -/

/-- The generic relation transports along a boundary cast on BOTH sides.  Mirrors
`IdempotentMonadSaturatedTwoCellConv.castBoundaryCongr`. -/
theorem castBoundaryCongrGen
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath monadGraph MonadMode.point MonadMode.point}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    {cellAlpha cellBeta : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    (conv : SaturatedConvOver monadModeSignature IdempotentLawRel cellAlpha cellBeta) :
    SaturatedConvOver monadModeSignature IdempotentLawRel (RawTwoCellExpr.castBoundary hsource htarget cellAlpha)
      (RawTwoCellExpr.castBoundary hsource htarget cellBeta) := by
  cases hsource; cases htarget; exact conv

/-- Move a boundary cast ACROSS the generic relation.  Mirrors `IdempotentMonadSaturatedTwoCellConv.ofCastLeft`. -/
theorem ofCastLeftGen
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath monadGraph MonadMode.point MonadMode.point}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    {cellAlpha : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    {cellBeta : RawTwoCellExpr monadModeSignature sourcePath' targetPath'}
    (conv : SaturatedConvOver monadModeSignature IdempotentLawRel
      (RawTwoCellExpr.castBoundary hsource htarget cellAlpha) cellBeta) :
    SaturatedConvOver monadModeSignature IdempotentLawRel cellAlpha
      (RawTwoCellExpr.castBoundary hsource.symm htarget.symm cellBeta) := by
  cases hsource; cases htarget; exact conv

/-- Extrude a LEFT-factor boundary cast out of a vertical composite.  Mirrors
`IdempotentMonadSaturatedTwoCellConv.vcompCastLeftExtrude`. -/
theorem vcompCastLeftExtrudeGen
    {sourcePath sourcePath' middlePath middlePath' targetPath :
      ModalityPath monadGraph MonadMode.point MonadMode.point}
    (hsource : sourcePath = sourcePath') (hmiddle : middlePath = middlePath')
    (cellAlpha : RawTwoCellExpr monadModeSignature sourcePath middlePath)
    (cellBeta : RawTwoCellExpr monadModeSignature middlePath' targetPath) :
    SaturatedConvOver monadModeSignature IdempotentLawRel
      (RawTwoCellExpr.vcomp (RawTwoCellExpr.castBoundary hsource hmiddle cellAlpha) cellBeta)
      (RawTwoCellExpr.castBoundary hsource rfl
        (RawTwoCellExpr.vcomp cellAlpha (RawTwoCellExpr.castBoundary hmiddle.symm rfl cellBeta))) := by
  cases hsource; cases hmiddle; exact SaturatedConvOver.refl _

/-! ## Brick 1 — general-width left-whisker canonicalisation -/

/-- ★ **General-width left-whisker canonicalisation**, generic-native —
`t^k <| (canonThroughT a n) ~ canonThroughT (a+k)(n+k)` (transported).  Mirrors `whiskerLeftCanon`. -/
theorem whiskerLeftCanonGen : (k a n : Nat) →
    SaturatedConvOver monadModeSignature IdempotentLawRel
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) (monadTPower k) (canonThroughT a n))
      (RawTwoCellExpr.castBoundary (monadTPower_add_left k a) (monadTPower_succ_add_left k n)
        (canonThroughT (a + k) (n + k)))
  | 0, a, n => idemFull (TwoCellConvFull.whiskerLeftUnit (canonThroughT a n))
  | k + 1, a, n => by
      show SaturatedConvOver monadModeSignature IdempotentLawRel
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature)
          (composePath monadT (monadTPower k)) (canonThroughT a n)) _
      refine trans
        (idemFull (TwoCellConvFull.whiskerLeftComp monadT (monadTPower k) (canonThroughT a n))) ?_
      refine trans
        (castBoundaryCongrGen _ _
          (whiskerLeftCongr monadT (whiskerLeftCanonGen k a n))) ?_
      rw [RawTwoCellExpr.whiskerLeft_castBoundary]
      refine trans
        (castBoundaryCongrGen _ _
          (castBoundaryCongrGen _ _
            (whiskerLeftCanonOneGen (a + k) (n + k)))) ?_
      rw [RawTwoCellExpr.castBoundary_castBoundary]
      exact SaturatedConvOver.refl _

/-! ## Brick 2 — the RIGHT-leaning mu-tree peel `gadgetSplitRightGen` -/

/-- Base `a = 0` of `gadgetSplitRightGen` — the LEFT-unit monad law.  Mirrors `gadgetSplitRight_zero`. -/
theorem gadgetSplitRightGenZero :
    SaturatedConvOver monadModeSignature IdempotentLawRel
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT (monadGadget 0))
        monadMulTwoCell)
      (RawTwoCellExpr.castBoundary (composePath_monadTPower_monadT 0).symm rfl (monadGadget 1)) :=
  idemLeftUnitLaw

/-- Base `a = 1` of `gadgetSplitRightGen`.  Mirrors `gadgetSplitRight_one`. -/
theorem gadgetSplitRightGenOne :
    SaturatedConvOver monadModeSignature IdempotentLawRel
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT (monadGadget 1))
        monadMulTwoCell)
      (RawTwoCellExpr.castBoundary (composePath_monadTPower_monadT 1).symm rfl (monadGadget 2)) := by
  refine trans
    (vcompCongrLeft monadMulTwoCell
      (idemStep (TwoCellStep.whiskerRightId (signature := monadModeSignature) monadT monadT))) ?_
  refine trans
    (idemStep (TwoCellStep.vcompIdLeft monadMulTwoCell)) ?_
  refine SaturatedConvOver.symm ?_
  show SaturatedConvOver monadModeSignature IdempotentLawRel
    (RawTwoCellExpr.vcomp
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
        (RawTwoCellExpr.id (signature := monadModeSignature) monadT))
      monadMulTwoCell)
    monadMulTwoCell
  refine trans
    (vcompCongrLeft monadMulTwoCell
      (idemStep (TwoCellStep.whiskerLeftId (signature := monadModeSignature) monadT monadT))) ?_
  exact idemStep (TwoCellStep.vcompIdLeft monadMulTwoCell)

/-- **The whisker braid**, generic-native — `(t <| g |> t) . (t <| mu) ~ t <| ((g |> t) . mu)` (transported).
Mirrors `whiskerRightLeftBraid`. -/
theorem whiskerRightLeftBraidGen {gDom : ModalityPath monadGraph MonadMode.point MonadMode.point}
    (g : RawTwoCellExpr monadModeSignature gDom monadT) :
    SaturatedConvOver monadModeSignature IdempotentLawRel
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT g))
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadMulTwoCell))
      (RawTwoCellExpr.castBoundary (composePath_assoc monadT gDom monadT).symm rfl
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
          (RawTwoCellExpr.vcomp
            (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT g) monadMulTwoCell))) := by
  have hbase : SaturatedConvOver monadModeSignature IdempotentLawRel
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT g) monadMulTwoCell))
      (RawTwoCellExpr.castBoundary (composePath_assoc monadT gDom monadT) rfl
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT
            (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT g))
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadMulTwoCell))) := by
    refine trans
      (idemStep (TwoCellStep.whiskerLeftVcomp monadT
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT g) monadMulTwoCell)) ?_
    refine trans
      (vcompCongrLeft _
        (idemFull (TwoCellConvFull.whiskerExchange monadT monadT g))) ?_
    rw [RawTwoCellExpr.vcomp_castBoundaryLeft]
    exact SaturatedConvOver.refl _
  exact ofCastLeftGen (composePath_assoc monadT gDom monadT) rfl
    (SaturatedConvOver.symm hbase)

/-- ★★ **The RIGHT-leaning mu-tree peel**, generic-native — `(monadGadget a |> t) . mu ~ monadGadget (a+1)`
(transported).  Mirrors `gadgetSplitRight`. -/
theorem gadgetSplitRightGen : (a : Nat) →
    SaturatedConvOver monadModeSignature IdempotentLawRel
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT (monadGadget a))
        monadMulTwoCell)
      (RawTwoCellExpr.castBoundary (composePath_monadTPower_monadT a).symm rfl (monadGadget (a + 1)))
  | 0 => gadgetSplitRightGenZero
  | 1 => gadgetSplitRightGenOne
  | a + 2 => by
      show SaturatedConvOver monadModeSignature IdempotentLawRel
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT
            (RawTwoCellExpr.vcomp
              (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (a + 1)))
              monadMulTwoCell))
          monadMulTwoCell)
        (RawTwoCellExpr.castBoundary (composePath_monadTPower_monadT (a + 2)).symm rfl (monadGadget (a + 3)))
      refine trans
        (vcompCongrLeft monadMulTwoCell
          (idemStep (TwoCellStep.whiskerRightVcomp monadT
            (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (a + 1)))
            monadMulTwoCell))) ?_
      refine trans
        (idemStep (TwoCellStep.vcompAssoc
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT
            (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (a + 1))))
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadMulTwoCell)
          monadMulTwoCell)) ?_
      refine trans
        (vcompCongrRight _
          idemAssocLaw) ?_
      refine trans
        (SaturatedConvOver.symm (idemStep (TwoCellStep.vcompAssoc
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT
            (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (a + 1))))
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadMulTwoCell)
          monadMulTwoCell))) ?_
      have hpull := monadWhiskerLeft_castBoundary
        (composePath_monadTPower_monadT (a + 1)).symm (rfl : monadT = monadT) (monadGadget (a + 1 + 1))
      have hpullConv : SaturatedConvOver monadModeSignature IdempotentLawRel
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
            (RawTwoCellExpr.castBoundary (composePath_monadTPower_monadT (a + 1)).symm rfl
              (monadGadget (a + 1 + 1))))
          (RawTwoCellExpr.castBoundary
            (congrArg (composePath monadT) (composePath_monadTPower_monadT (a + 1)).symm) rfl
            (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (a + 1 + 1)))) :=
        hpull ▸ SaturatedConvOver.refl _
      refine SaturatedConvOver.trans
        (vcompCongrLeft monadMulTwoCell
          (whiskerRightLeftBraidGen (monadGadget (a + 1)))) ?_
      have innerConv :
          SaturatedConvOver monadModeSignature IdempotentLawRel
            (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
              (RawTwoCellExpr.vcomp
                (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT (monadGadget (a + 1)))
                monadMulTwoCell))
            (RawTwoCellExpr.castBoundary
              (congrArg (composePath monadT) (composePath_monadTPower_monadT (a + 1)).symm) rfl
              (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
                (monadGadget (a + 1 + 1)))) :=
        SaturatedConvOver.trans
          (whiskerLeftCongr monadT (gadgetSplitRightGen (a + 1)))
          hpullConv
      refine SaturatedConvOver.trans (vcompCongrLeft monadMulTwoCell innerConv) ?_
      refine SaturatedConvOver.trans
        (vcompCastLeftExtrudeGen _ _ _ monadMulTwoCell) ?_
      exact SaturatedConvOver.refl _

end FX1Poly.Polygraph.Amalgam
