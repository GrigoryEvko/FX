import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentSaturatedMuInvertible

/-! # WalkingIdempotent/IdempotentSaturatedLadder — the fold/grow ladder, GENERIC-NATIVE

The general-`n` mu-iso tower iterate re-founded DIRECTLY over `SaturatedConvOver monadModeSignature IdempotentLawRel`
(never the bespoke `IdempotentMonadSaturatedTwoCellConv`).  Mirrors `IdempotentMonadNormalizer` arm-for-arm.  The
conv-FREE defs (`growTower`, `canonThroughT`, `monadGadget`, `monadTPower`) are REUSED verbatim from the bespoke lane.

Raw Lean 4 + Init; STRUCTURAL `Nat` recursion; every proof BUILDS conv values.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration `#assert_no_axioms` gated
in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph
open SaturatedConvOver

/-! ## The fold-then-grow round-trip (the idempotence iterate) -/

/-- ★★ **Fold-then-grow ~ identity**, generic-native — `(monadGadget (k+1)) . (growTower k) ~ id_{t^{k+1}}`.
Mirrors `foldThenGrow`. -/
theorem foldThenGrowGen : (k : Nat) →
    SaturatedConvOver monadModeSignature IdempotentLawRel
      (RawTwoCellExpr.vcomp (monadGadget (k + 1)) (growTower k))
      (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower (k + 1)))
  | 0 => by
      show SaturatedConvOver monadModeSignature IdempotentLawRel
        (RawTwoCellExpr.vcomp (RawTwoCellExpr.id (signature := monadModeSignature) monadT)
          (RawTwoCellExpr.id (signature := monadModeSignature) monadT))
        (RawTwoCellExpr.id (signature := monadModeSignature) monadT)
      exact idemStep
        (TwoCellStep.vcompIdLeft (RawTwoCellExpr.id (signature := monadModeSignature) monadT))
  | k + 1 => by
      show SaturatedConvOver monadModeSignature IdempotentLawRel
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.vcomp
            (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (k + 1)))
            monadMulTwoCell)
          (RawTwoCellExpr.vcomp monadEtaTCell
            (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (growTower k))))
        (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower (k + 1 + 1)))
      refine trans (idemStep (TwoCellStep.vcompAssoc
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (k + 1)))
        monadMulTwoCell
        (RawTwoCellExpr.vcomp monadEtaTCell
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (growTower k))))) ?_
      refine trans (vcompCongrRight _ (symm (idemStep (TwoCellStep.vcompAssoc
        monadMulTwoCell monadEtaTCell
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (growTower k)))))) ?_
      refine trans (vcompCongrRight _ (vcompCongrLeft _ idempotentMulRightInverse_gen)) ?_
      refine trans (vcompCongrRight _ (idemStep (TwoCellStep.vcompIdLeft
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (growTower k))))) ?_
      refine trans (symm (idemStep (TwoCellStep.whiskerLeftVcomp
        monadT (monadGadget (k + 1)) (growTower k)))) ?_
      refine trans (whiskerLeftCongr monadT (foldThenGrowGen k)) ?_
      show SaturatedConvOver monadModeSignature IdempotentLawRel
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
          (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower (k + 1))))
        (RawTwoCellExpr.id (signature := monadModeSignature) (composePath monadT (monadTPower (k + 1))))
      exact idemStep
        (TwoCellStep.whiskerLeftId (signature := monadModeSignature) monadT (monadTPower (k + 1)))

/-! ## The grow-then-fold round-trip (the dual, via the left-unit law) -/

/-- ★★ **Grow-then-fold ~ identity**, generic-native — `(growTower g) . (monadGadget (g+1)) ~ id_t`.
Mirrors `growThenFold`. -/
theorem growThenFoldGen : (g : Nat) →
    SaturatedConvOver monadModeSignature IdempotentLawRel
      (RawTwoCellExpr.vcomp (growTower g) (monadGadget (g + 1)))
      (RawTwoCellExpr.id (signature := monadModeSignature) monadT)
  | 0 => by
      show SaturatedConvOver monadModeSignature IdempotentLawRel
        (RawTwoCellExpr.vcomp (RawTwoCellExpr.id (signature := monadModeSignature) monadT)
          (RawTwoCellExpr.id (signature := monadModeSignature) monadT))
        (RawTwoCellExpr.id (signature := monadModeSignature) monadT)
      exact idemStep
        (TwoCellStep.vcompIdLeft (RawTwoCellExpr.id (signature := monadModeSignature) monadT))
  | g + 1 => by
      show SaturatedConvOver monadModeSignature IdempotentLawRel
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.vcomp monadEtaTCell
            (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (growTower g)))
          (RawTwoCellExpr.vcomp
            (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (g + 1)))
            monadMulTwoCell))
        (RawTwoCellExpr.id (signature := monadModeSignature) monadT)
      refine trans (idemStep (TwoCellStep.vcompAssoc
        monadEtaTCell
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (growTower g))
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (g + 1)))
          monadMulTwoCell))) ?_
      refine trans (vcompCongrRight _ (symm (idemStep (TwoCellStep.vcompAssoc
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (growTower g))
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (g + 1)))
        monadMulTwoCell)))) ?_
      refine trans (vcompCongrRight _ (vcompCongrLeft _
        (symm (idemStep (TwoCellStep.whiskerLeftVcomp
          monadT (growTower g) (monadGadget (g + 1))))))) ?_
      refine trans (vcompCongrRight _ (vcompCongrLeft _
        (whiskerLeftCongr monadT (growThenFoldGen g)))) ?_
      refine trans (vcompCongrRight _ (vcompCongrLeft _
        (idemStep (TwoCellStep.whiskerLeftId (signature := monadModeSignature) monadT monadT)))) ?_
      refine trans (vcompCongrRight _ (idemStep (TwoCellStep.vcompIdLeft monadMulTwoCell))) ?_
      show SaturatedConvOver monadModeSignature IdempotentLawRel monadLeftUnitCell
        (RawTwoCellExpr.id (signature := monadModeSignature) monadT)
      exact idemLeftUnitLaw

/-! ## Single-`t` LEFT-whisker canonicalisation -/

/-- **Fold-whisker step**, generic-native — `(t <| (monadGadget a)) . mu ~ monadGadget (a+1)`.
Mirrors `foldWhiskerStep`. -/
theorem foldWhiskerStepGen : (a : Nat) →
    SaturatedConvOver monadModeSignature IdempotentLawRel
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget a))
        monadMulTwoCell)
      (monadGadget (a + 1))
  | 0 => by
      show SaturatedConvOver monadModeSignature IdempotentLawRel monadRightUnitCell
        (RawTwoCellExpr.id (signature := monadModeSignature) monadT)
      exact idemRightUnitLaw
  | a + 1 =>
      SaturatedConvOver.refl
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (a + 1)))
          monadMulTwoCell)

/-- ★ **Single-`t` LEFT-whisker canonicalisation**, generic-native —
`t <| (canonThroughT a tp) ~ canonThroughT (a+1) (tp+1)`.  Mirrors `whiskerLeftCanonOne`. -/
theorem whiskerLeftCanonOneGen (sourceCount targetPred : Nat) :
    SaturatedConvOver monadModeSignature IdempotentLawRel
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
        (canonThroughT sourceCount targetPred))
      (canonThroughT (sourceCount + 1) (targetPred + 1)) := by
  show SaturatedConvOver monadModeSignature IdempotentLawRel
    (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
      (RawTwoCellExpr.vcomp (monadGadget sourceCount) (growTower targetPred)))
    (RawTwoCellExpr.vcomp (monadGadget (sourceCount + 1)) (growTower (targetPred + 1)))
  refine trans (idemStep
    (TwoCellStep.whiskerLeftVcomp monadT (monadGadget sourceCount) (growTower targetPred))) ?_
  refine trans (vcompCongrRight _ (symm (idemStep
    (TwoCellStep.vcompIdLeft
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (growTower targetPred)))))) ?_
  refine trans (vcompCongrRight _
    (vcompCongrLeft _ (symm idempotentMulRightInverse_gen))) ?_
  refine trans (vcompCongrRight _ (idemStep
    (TwoCellStep.vcompAssoc monadMulTwoCell monadEtaTCell
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (growTower targetPred))))) ?_
  refine trans (symm (idemStep
    (TwoCellStep.vcompAssoc
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget sourceCount))
      monadMulTwoCell
      (RawTwoCellExpr.vcomp monadEtaTCell
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (growTower targetPred)))))) ?_
  exact vcompCongrLeft _ (foldWhiskerStepGen sourceCount)

end FX1Poly.Polygraph.Amalgam
