import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadNormalizeVcomp
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadLawRelation
import FX1Poly.Polygraph.TwoCategory.Amalgam.DispatchSaturated

import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadWordMultGen

/-! # WalkingMonad/MonadNormalizeCasesGen — the base + id `normalize` cases over the GENERIC carrier
(POLY-TAB r6 monad re-founding, WAVE 2, Brick A)

The two generator leaves (`gen eta` / `gen mu`), the `id` case, and the ones-word collapse, re-founded over
`SaturatedConvOver monadModeSignature MonadLawRel`.  Free-strict-2-category only — no monad law.  The carrier-only
`countsOf`/`canon`/cast lemmas are REUSED.

Raw Lean 4 + Init; zero-axiom; STRUCTURAL.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The generator base cases + the id case, generic carrier -/

/-- ★ **Base case — the unit `eta`.**  `gen eta ≈ canon (gen eta)`.  Its fold is `[]`, so the canonical count list
is `[0]` and `canon (gen eta)` is DEFINITIONALLY `wordFromCounts [0] = hcomp (monadGadget 0) (id t^0) = vcomp
(whiskerRight t^0 eta) (whiskerLeft t (id t^0))` (the boundary cast is definitionally the identity — both boundaries
are `nil` / `monadT` on the nose).  Strip the trailing left-whisker identity by `whiskerLeftId` + `vcompIdRight`,
then the right-whisker-unit on `eta` by `whiskerRightUnit`, using ONLY the free-2-category structural laws. -/
theorem monadNormalize_genEtaGen :
    SaturatedConvOver monadModeSignature MonadLawRel (RawTwoCellExpr.gen MonadTwoCell.eta)
      (canon (RawTwoCellExpr.gen MonadTwoCell.eta)) := by
  refine SaturatedConvOver.symm ?_
  show SaturatedConvOver monadModeSignature MonadLawRel
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower 0) monadUnitTwoCell)
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
          (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower 0))))
      (RawTwoCellExpr.gen MonadTwoCell.eta)
  have hRight : SaturatedConvOver monadModeSignature MonadLawRel
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
        (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower 0)))
      (RawTwoCellExpr.id (signature := monadModeSignature) (composePath monadT (monadTPower 0))) :=
    SaturatedConvOver.ofConv (baseRel := MonadLawRel) (TwoCellConv.ofStep (TwoCellStep.whiskerLeftId (signature := monadModeSignature) monadT (monadTPower 0)))
  refine SaturatedConvOver.trans
    (SaturatedConvOver.vcompCongrRight
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower 0) monadUnitTwoCell) hRight) ?_
  refine SaturatedConvOver.trans
    (SaturatedConvOver.ofConv (baseRel := MonadLawRel) (TwoCellConv.ofStep
      (TwoCellStep.vcompIdRight
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower 0) monadUnitTwoCell)))) ?_
  exact SaturatedConvOver.ofFull (baseRel := MonadLawRel) (TwoCellConvFull.whiskerRightUnit monadUnitTwoCell)

/-- ★ **Base case — the multiplication `mu`.**  `gen mu ≈ canon (gen mu)`.  Its fold is `[0,0]`, so the canonical
count list is `[2]` and `canon (gen mu)` is DEFINITIONALLY `wordFromCounts [2] = hcomp (monadGadget 2) (id t^0) =
vcomp (whiskerRight t^0 (monadGadget 2)) (whiskerLeft t (id t^0))`.  Strip the trailing left-whisker identity
(`whiskerLeftId` + `vcompIdRight`) and the right-whisker-unit (`whiskerRightUnit`) to reach `monadGadget 2`, then
collapse `monadGadget 2 = vcomp (whiskerLeft t (id t)) mu` to `mu`: the inner `whiskerLeft t (id t)` is the identity
on `t·t` (`whiskerLeftId`), dropped by `vcompIdLeft`.  Purely free-2-category structural — no monad law. -/
theorem monadNormalize_genMuGen :
    SaturatedConvOver monadModeSignature MonadLawRel (RawTwoCellExpr.gen MonadTwoCell.mu)
      (canon (RawTwoCellExpr.gen MonadTwoCell.mu)) := by
  refine SaturatedConvOver.symm ?_
  show SaturatedConvOver monadModeSignature MonadLawRel
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower 0) (monadGadget 2))
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
          (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower 0))))
      (RawTwoCellExpr.gen MonadTwoCell.mu)
  -- Strip the trailing left-whisker identity.
  have hRight : SaturatedConvOver monadModeSignature MonadLawRel
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
        (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower 0)))
      (RawTwoCellExpr.id (signature := monadModeSignature) (composePath monadT (monadTPower 0))) :=
    SaturatedConvOver.ofConv (baseRel := MonadLawRel) (TwoCellConv.ofStep (TwoCellStep.whiskerLeftId (signature := monadModeSignature) monadT (monadTPower 0)))
  refine SaturatedConvOver.trans
    (SaturatedConvOver.vcompCongrRight
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower 0) (monadGadget 2)) hRight) ?_
  refine SaturatedConvOver.trans
    (SaturatedConvOver.ofConv (baseRel := MonadLawRel) (TwoCellConv.ofStep
      (TwoCellStep.vcompIdRight
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower 0) (monadGadget 2))))) ?_
  -- Strip the right-whisker-unit: whiskerRight (t^0) (monadGadget 2) ≈ monadGadget 2.
  refine SaturatedConvOver.trans
    (SaturatedConvOver.ofFull (baseRel := MonadLawRel) (TwoCellConvFull.whiskerRightUnit (monadGadget 2))) ?_
  -- Collapse monadGadget 2 = vcomp (whiskerLeft t (id t)) mu to mu.
  show SaturatedConvOver monadModeSignature MonadLawRel
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
          (RawTwoCellExpr.id (signature := monadModeSignature) monadT))
        monadMulTwoCell)
      (RawTwoCellExpr.gen MonadTwoCell.mu)
  have hInner : SaturatedConvOver monadModeSignature MonadLawRel
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
        (RawTwoCellExpr.id (signature := monadModeSignature) monadT))
      (RawTwoCellExpr.id (signature := monadModeSignature) (composePath monadT monadT)) :=
    SaturatedConvOver.ofConv (baseRel := MonadLawRel) (TwoCellConv.ofStep (TwoCellStep.whiskerLeftId (signature := monadModeSignature) monadT monadT))
  refine SaturatedConvOver.trans
    (SaturatedConvOver.vcompCongrLeft monadMulTwoCell hInner) ?_
  exact SaturatedConvOver.ofConv (baseRel := MonadLawRel) (TwoCellConv.ofStep (TwoCellStep.vcompIdLeft monadMulTwoCell))

/-- ★ **Case `id path` of `normalize`.**  Every identity 2-cell is saturated-convertible to the canonical word of
its own fold: `id path ≈ canon (id path)`.  `canonCounts (id path) = countsOf path.length 0 (idMap path.length) =
monadOnes path.length` (`countsOf_ascendingFrom_ones`), so `canon (id path)` is the boundary-transported ones word;
that word collapses to the identity (`wordFromCounts_monadOnes_convGen`), and the nested boundary casts fuse
(`castBoundary_castBoundary`) and cancel on the identity (`monadCastBoundary_id`).  Purely free-2-category — no monad
law. -/
theorem monadNormalize_idGen (path : ModalityPath monadGraph MonadMode.point MonadMode.point) :
    SaturatedConvOver monadModeSignature MonadLawRel (RawTwoCellExpr.id (signature := monadModeSignature) path)
      (canon (RawTwoCellExpr.id (signature := monadModeSignature) path)) := by
  have hcountsEq : canonCounts (RawTwoCellExpr.id (signature := monadModeSignature) path)
      = monadOnes path.length := by
    show countsOf path.length 0 (ascendingFrom 0 path.length) = monadOnes path.length
    exact countsOf_ascendingFrom_ones path.length 0
  have hdomRight : countsDomainPath (monadOnes path.length) = path :=
    (countsDomainPath_monadOnes path.length).trans (monadPath_normalForm path).symm
  have hcodRight : monadTPower (monadOnes path.length).length = path :=
    (congrArg monadTPower (length_monadOnes path.length)).trans (monadPath_normalForm path).symm
  have hcanon : canon (RawTwoCellExpr.id (signature := monadModeSignature) path)
      = RawTwoCellExpr.castBoundary hdomRight hcodRight (wordFromCounts (monadOnes path.length)) :=
    RawTwoCellExpr.castBoundary_wordCongr
      (canonDomain_eq (RawTwoCellExpr.id (signature := monadModeSignature) path))
      (canonCodomain_eq (RawTwoCellExpr.id (signature := monadModeSignature) path))
      hdomRight hcodRight hcountsEq
  have collapse : SaturatedConvOver monadModeSignature MonadLawRel
      (RawTwoCellExpr.castBoundary hdomRight hcodRight (wordFromCounts (monadOnes path.length)))
      (RawTwoCellExpr.id (signature := monadModeSignature) path) := by
    have hstep := SaturatedConvOver.castBoundaryCongr hdomRight hcodRight
      (wordFromCounts_monadOnes_convGen path.length)
    rw [monadCastBoundary_castBoundary, monadCastBoundary_id] at hstep
    exact hstep
  rw [hcanon]
  exact SaturatedConvOver.symm collapse

/-- **ESTABLISHED — the two generator base cases + the `id` case of `normalize` are re-founded GENERIC-NATIVE.**
`monadNormalize_genEtaGen` / `monadNormalize_genMuGen` / `monadNormalize_idGen`, bespoke-free.  `= true`. -/
def fxMonad_hasNormalizeBaseCasesGen : Bool := true

end FX1Poly.Polygraph.Amalgam
