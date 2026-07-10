import FX1Poly.Polygraph.TwoCategory.Amalgam.ReconstructedDecision
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutBundle
import FX1Poly.Polygraph.TwoCategory.Amalgam.ConvFullFunctorDispatch

/-! # Polygraph/TwoCategory/Amalgam/RealLawDispatch — the REAL-law pushout dispatch, SOUNDNESS half
(WP-AMALG-2 r2, the 110-percent grind: #2043)

r1 (`Modularity.lean` / `DispatchLedger.lean`) shipped modularity + a live combined decider ONLY for the
provably-EMPTY law fragment (`fxAmalg_hasComposableFragmentDispatch`, `fxAmalg_hasModularityDisjointScope`): the
crossing-law relation was `emptyCellRel`, so every `ofRelation` was `False.elim`.  r8 (`PushoutBundle.lean`) shipped
the arity-fold reflection and the UNCONDITIONAL `isFalse` on the specific interleaving pair — but still over the
EMPTY-component base relation `crossPairPushoutRel`.  This file lifts BOTH the reflection and the separation from the
empty relation to the REAL walking-monad law relation `MonadLawRelReconstructed` on the right component (the
involution left stays thin/empty), and packages the two verdict SHAPES the recon named.

## The headline finding, executed (Route B — the semantic model)

The row of `SaturatedConvOverPushout` injects the BARE coprojected component-law pair (`DispatchSaturated.lean`
`left`/`right`, no whisker context baked in), so a law redex `ofRelation (right law)` is INTRINSICALLY mono-component
by construction — its two sides are `mapCellAlong inclRight a` / `mapCellAlong inclRight b` for a component-2 law
`a ~ b`.  "Locality" (a law window commutes past a foreign block) is therefore FREE / structural: there is nothing
to commute, and the interleaving lives entirely in the OUTER `SaturatedConvOver` congruence closure, whose whisker/
vcomp congruences the shipped bundle `pushoutArityFoldConvSound` (r8) already handles.  The whole round's genuine
content collapses to ONE lemma: the coprojected REAL law preserves the payload-blind arity fold
`arityMonotoneMapOf`.  And that is discharged by COMPUTATION — the fold reads the spine only through the three
lengths `leftContext.length` / `generatorDom.length` / `generatorCod.length`, so `mapCellAlong` (which retags
generators, keeping arity `(0,1)` for `eta` and `(2,1)` for `mu`) leaves the fold definitionally unchanged, and the
three concrete monad laws all fold LHS = RHS (`[0] = [0]`, `[0] = [0]`, `[0,0,0] = [0,0,0]`).

## The bricks (WP-AMALG-2 r2)

  * **B1 — THE LAW-REDEX LOCALITY LEMMA** (`monadLawReconstructed_arityEq`, `arityFoldEqRel_of_realPushoutRow`).
    The mono-component law soundness: a reconstructed monad-law row preserves the arity fold (each row by `rfl`,
    the fold being payload-blind); lifted to the pushout, the REAL coprojected law row preserves `arityFoldEqRel`
    (the `right` arm cases the three laws to `rfl`; the `left` arm is `involutionRow.elim`, involution being thin).
    This is the drop-in real-law replacement for the r7 `arityFoldEqRel_of_emptyPushoutRow` (which was
    `False.elim` on both arms).  Non-vacuity on a real interleaved firing: `sInterleavedAssocLawConv` (B2).

  * **B2 — THE SATURATED BLOCK LIFT, both directions.**  SOUNDNESS whisker-lift: `sInterleavedAssocLawConv` /
    `sInterleavedLeftUnitLawConv` — a REAL monad law fired inside an `s`-interleaved word `s · (law) · …`, built by
    whiskering `pushoutPreservesConvRight` (the shipped unconditional right-coprojection soundness lift) on the left
    by the component-1 `s`-path.  A live, hypothesis-FREE `SaturatedConvOver pushout (real rel)` inhabitant of a
    genuinely-interleaved cell whose interior fires a REAL monad law.  COMPLETENESS decomposition (riding B1):
    `arityFoldRealPushoutCongruence` — the real-law analogue of the r7 `arityFoldPushoutCongruence`, whose
    `ofRelation` leg is B1 and whose every other field is the shipped `pushoutArityFoldConvSound`.

  * **B3 — THE COMPOSED DECISION (isFalse, unconditional).**  `crossPairRealPushoutNonConv` — the real
    involution +_M monad pushout SEPARATES the interleaving pair `crossPairAlpha` (`δ₁` whiskered by `s`) /
    `crossPairBeta` (`δ₀` whiskered by `s`), HYPOTHESIS-FREE, by recursion through `arityFoldRealPushoutCongruence`
    forcing `[0,2] = [0,1]` against `crossPair_arityMapsDiffer`.  This is the r8
    `crossPairPushoutNonConvUnconditional` LIFTED from the empty-component base relation to the REAL
    `MonadLawRelReconstructed` — the genuine advance over r1 (which decided only the empty-law fragment).  Both
    verdict shapes stand together: this real-law `isFalse` (separating) against the real-law `isTrue` witnesses of
    B2 (a real law fired in an interleaved word).

## What this is, and what it is NOT (#2043 does NOT close — the honest verdict)

This ships the SOUNDNESS half of the real-law dispatch: the semantic invariant `arityMonotoneMapOf` reflects the
crossing monad-law inequality DIRECTLY (the categorical Nelson-Oppen soundness — the projecting direction needs no
convexity), so the separating verdict is TOTAL and unconditional over real laws, and the convertible verdict is
witnessed on real interleaved firings.  It does NOT ship a TOTAL two-sided `Decidable` for arbitrary pushout pairs:
the `isTrue` COMPLETENESS for an arbitrary convertible pair (equal fold ⟹ pushout-convertible) needs a pushout
NORMAL FORM weaving the monad Eilenberg-Zilber NF through the involution `s`-whisker contexts, and the monad
unit/mult WIRE-CREATING generators break the convex-block projection (`DispatchSaturated.lean` residual (iii)).
So `fxAmalg_hasFullSaturatedPushoutDispatch` (`DispatchSaturated.lean`) STAYS `false` — untouched — and
`fxAmalg_hasGeneralPushoutDispatch` (`PushoutBundle.lean`) STAYS `false`.  #2043 remains OPEN, its wall now NARROWED
to reverse-completeness / pushout NF alone (r3 / WP-AMALG-3 territory).  No fabricated flip.

Literature: free-product / Δ₊ word problem (Nyberg-Brodda; Street "formal theory of monads"; Mac Lane §VII.5); the
soundness direction of Nelson-Oppen combination (Baader-Tinelli 1998; Pigozzi 1974) — sound without the
stably-infinite / convexity side condition, which is exactly the reverse (completeness) obligation.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## B1 — the law-redex locality lemma: the mono-component monad law preserves the arity fold -/

/-- ★ **The reconstructed monad-law rows preserve the arity fold** — each of the three walking-monad laws relates a
pair of parallel reconstructed 2-cells that fold to the SAME `arityMonotoneMapOf` (`leftUnit` / `rightUnit` both
`[0] = [0]`; `assoc` `[0,0,0] = [0,0,0]`), by `rfl`, because the fold reads only the arity/position spine and is
blind to the generator payload.  This is the "law window is mono-component" content of the recon, discharged by
COMPUTATION rather than a Godement / trace argument: the redex is intrinsically mono-component (the row carries a
bare component-2 law), so its two sides fold identically.  The base-relation-level soundness the pushout lemma
lifts. -/
theorem monadLawReconstructed_arityEq
    {sourceMode targetMode : monadComputad.toModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath monadComputad.toModeSignature.graph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr monadComputad.toModeSignature sourcePath targetPath}
    (law : MonadLawRelReconstructed cellA cellB) :
    arityMonotoneMapOf cellA = arityMonotoneMapOf cellB := by
  cases law with
  | leftUnit => rfl
  | rightUnit => rfl
  | assoc => rfl

/-- ★ **The REAL-law pushout base relation** — the involution +_M monad pushout with the LEFT (involution, thin)
component relation EMPTY and the RIGHT component relation the genuine `MonadLawRelReconstructed`.  The real-law
analogue of r7's `crossPairPushoutRel` (which had BOTH component relations empty).  Its `left` rows carry an
`emptyCellRel` (unfireable, involution being thin); its `right` rows carry a genuine reconstructed monad law. -/
abbrev crossPairRealPushoutRel : CellRel involutionMonadPushout.toModeSignature :=
  SaturatedConvOverPushout involutionComputad monadComputad involutionMonadSameModes
    (inclusionLeftTwo involutionComputad monadComputad involutionMonadSameModes rfl)
    (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes)
    (emptyCellRel involutionComputad.toModeSignature)
    MonadLawRelReconstructed

/-- ★★ **THE LAW-REDEX LOCALITY LEMMA (B1).**  A REAL coprojected law row of the pushout preserves the arity fold —
the drop-in real-law replacement for the r7 `arityFoldEqRel_of_emptyPushoutRow` (pure `False.elim`).  The `left`
arm is vacuous (`involutionRow.elim`, the involution component relation being empty/thin); the `right` arm receives
a genuine `MonadLawRelReconstructed a b` whose two sides in the pushout are `mapCellAlong inclRight a` /
`mapCellAlong inclRight b`, and since `mapCellAlong` retags generators keeping their `(0,1)`/`(2,1)` arity and the
fold is payload-blind, each of the three laws folds LHS = RHS (`rfl`).  The locality is FREE: the redex window is
mono-component by construction, so there is no foreign block to commute past — the interleaving lives in the OUTER
congruence closure (handled by `pushoutArityFoldConvSound`). -/
theorem arityFoldEqRel_of_realPushoutRow
    {sourceMode targetMode : involutionMonadPushout.toModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath involutionMonadPushout.toModeSignature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr involutionMonadPushout.toModeSignature sourcePath targetPath}
    (row : crossPairRealPushoutRel cellAlpha cellBeta) :
    arityFoldEqRel cellAlpha cellBeta := by
  cases row with
  | left involutionRow => exact involutionRow.elim
  | right monadLaw =>
      cases monadLaw with
      | leftUnit => rfl
      | rightUnit => rfl
      | assoc => rfl

/-! ## B2 — the saturated block lift: the completeness decomposition (riding B1) -/

/-- ★★ **The real-law arity-fold congruence (B2, completeness decomposition).**  The arity-fold-equality relation
absorbs the REAL-law pushout saturated congruence: the `ofRelation` leg is B1
(`arityFoldEqRel_of_realPushoutRow`); the `ofFull` leg and the four one-hole congruences are the shipped
UNCONDITIONAL bundle `pushoutArityFoldConvSound` (r8); `refl`/`symm`/`trans` are `Eq`.  The real-law analogue of the
r7 `arityFoldPushoutCongruence` — identical everywhere except the `ofRelation` leg is now the genuine monad-law
soundness instead of `False.elim`.  Packaged for `SaturatedConvOver.recInto`: this is the projection that
decomposes any real-law pushout derivation into the semantic fold invariant. -/
def arityFoldRealPushoutCongruence :
    IsSaturatedCongruence involutionMonadPushout.toModeSignature crossPairRealPushoutRel arityFoldEqRel where
  ofFull full := arityMonotoneMapOf_eqOfConvFull pushoutArityFoldConvSound full
  ofRelation row := arityFoldEqRel_of_realPushoutRow row
  vcompCongrLeft {_ _ _ _ _ _ _ cellBeta} ih := pushoutArityFoldConvSound.vcompCongrLeft cellBeta ih
  vcompCongrRight {_ _ _ _ _ cellAlpha _ _} ih := pushoutArityFoldConvSound.vcompCongrRight cellAlpha ih
  whiskerLeftCongr {_ _ _ oneCell _ _ _ _} ih := pushoutArityFoldConvSound.whiskerLeftCongr oneCell ih
  whiskerRightCongr {_ _ _ _ _ oneCell _ _} ih := pushoutArityFoldConvSound.whiskerRightCongr oneCell ih
  refl _ := rfl
  symm ih := ih.symm
  trans ihLeft ihRight := ihLeft.trans ihRight

/-! ## B3 — the composed decision: the real-law separation, UNCONDITIONAL (isFalse) -/

/-- ★★★ **THE REAL-LAW COMBINED NON-CONVERTIBILITY (B3, isFalse), HYPOTHESIS-FREE.**  Over the REAL
involution +_M monad pushout (the LEFT involution law relation empty, the RIGHT the genuine
`MonadLawRelReconstructed`), the interleaving pair `crossPairAlpha` (`δ₁` whiskered by `s`) and `crossPairBeta`
(`δ₀` whiskered by `s`) are NOT saturated-convertible: `SaturatedConvOver.recInto` through
`arityFoldRealPushoutCongruence` forces their arity maps equal, contradicting `crossPair_arityMapsDiffer`
(`[0,2] ≠ [0,1]`).  This LIFTS r8's `crossPairPushoutNonConvUnconditional` from the empty-component base relation to
the REAL monad law relation — the genuine advance over the r1 empty-law-only modularity.  Pairs with the real-law
`isTrue` witnesses `sInterleavedAssocLawConv` / `sInterleavedLeftUnitLawConv` (a real law fired in an interleaved
word) as the complete discriminating pair over a real-relation pushout. -/
theorem crossPairRealPushoutNonConv :
    ¬ SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel
        crossPairAlpha crossPairBeta :=
  fun conv => crossPair_arityMapsDiffer
    (SaturatedConvOver.recInto arityFoldRealPushoutCongruence conv)

/-! ## B2 — the saturated block lift: the SOUNDNESS whisker-lift (isTrue witnesses)

The concrete `s-block · (law) · …` example the recon requested: a REAL monad law lifted into the pushout by the
shipped unconditional right-coprojection soundness lift (`pushoutPreservesConvRight`, whose base relation is the
REAL `SaturatedConvOverPushout … MonadLawRelReconstructed`), then whiskered on the LEFT by the component-1 `s`-path.
A live, hypothesis-free `SaturatedConvOver pushout (real rel)` inhabitant of a genuinely-interleaved cell whose
interior fires a REAL monad law.  These SHIP because they are the SOUNDNESS direction
(`fxAmalg_hasUnconditionalSoundnessLift`, `ConvFullFunctorDispatch.lean`). -/

/-- ★★ **The isTrue witness — a REAL monad ASSOCIATIVITY law fired inside an `s`-interleaved word.**  The
reconstructed associativity law `MonadLawRelReconstructed.assoc` (relating `reconAssocLeftCell` / `reconAssocRightCell`,
each `t·t·t ⇒ t`) is lifted along the real right coprojection to a pushout saturated convertibility of its
`mapCellAlong inclRight`-images (via `pushoutPreservesConvRight`), then whiskered on the left by the component-1
`s`-path — a live `s · (mu-assoc law) · …` inhabitant, the concrete `s-block · (law) · s-block` example.  Genuinely
interleaved (an `s` prefix over a coprojected monad-law tail) and firing a REAL monad law.  (The precise
convertibility type — `whiskerLeft s (mapCellAlong inclRight reconAssocLeftCell) ≈ whiskerLeft s (mapCellAlong
inclRight reconAssocRightCell)` over `crossPairRealPushoutRel` — is left to inference, surfaced by `#check`
below, exactly as the sibling `crossPairConvertibleCounterpart` is.) -/
def sInterleavedAssocLawConv :=
  SaturatedConvOver.whiskerLeftCongr (baseRel := crossPairRealPushoutRel) monadPushSPath
    (pushoutPreservesConvRight involutionMonadSameModes
      (inclusionLeftTwo involutionComputad monadComputad involutionMonadSameModes rfl)
      (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes)
      (emptyCellRel involutionComputad.toModeSignature)
      MonadLawRelReconstructed
      (SaturatedConvOver.ofRelation MonadLawRelReconstructed.assoc))

/-- ★★ **The isTrue witness — a REAL monad LEFT-UNIT law fired inside an `s`-interleaved word.**  The
reconstructed left-unit law `MonadLawRelReconstructed.leftUnit` (relating `reconLeftUnitCell` / `reconIdTCell`, each
`t ⇒ t`) lifted along the real right coprojection and whiskered on the left by `s` — a second live `s · (eta-unit
law) · …` inhabitant, a width-1 monad law fired in a genuinely-interleaved word.  (Type left to inference,
surfaced by `#check` below.) -/
def sInterleavedLeftUnitLawConv :=
  SaturatedConvOver.whiskerLeftCongr (baseRel := crossPairRealPushoutRel) monadPushSPath
    (pushoutPreservesConvRight involutionMonadSameModes
      (inclusionLeftTwo involutionComputad monadComputad involutionMonadSameModes rfl)
      (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes)
      (emptyCellRel involutionComputad.toModeSignature)
      MonadLawRelReconstructed
      (SaturatedConvOver.ofRelation MonadLawRelReconstructed.leftUnit))

/-! ## Observability -/

-- The three reconstructed monad laws fold LHS = RHS (payload-blind): expect `[0]`, `[0]`, `[0]`, `[0,0,0]`, `[0,0,0]`.
#eval arityMonotoneMapOf reconLeftUnitCell
#eval arityMonotoneMapOf reconIdTCell
#eval arityMonotoneMapOf reconAssocLeftCell
#eval arityMonotoneMapOf reconAssocRightCell
-- Each law preserves the fold; the interleaving pair still separates: expect `true`.
#eval decide (arityMonotoneMapOf reconLeftUnitCell = arityMonotoneMapOf reconIdTCell
  ∧ arityMonotoneMapOf reconAssocLeftCell = arityMonotoneMapOf reconAssocRightCell
  ∧ arityMonotoneMapOf crossPairAlpha ≠ arityMonotoneMapOf crossPairBeta)

-- The isTrue witness types: a REAL monad law fired inside an `s`-interleaved word over the REAL law relation.
#check @sInterleavedAssocLawConv
#check @sInterleavedLeftUnitLawConv

/-! ## Honesty markers -/

/-- ★★★ **Honesty marker — the REAL-LAW pushout dispatch SOUNDNESS half SHIPS (WP-AMALG-2 r2).**  `= true`: the
law-redex locality lemma (B1, `arityFoldEqRel_of_realPushoutRow`: the REAL coprojected monad law preserves the
payload-blind arity fold, each row by `rfl`, involution arm vacuous — the drop-in real-law replacement for r7's
`False.elim`-only `arityFoldEqRel_of_emptyPushoutRow`), the completeness decomposition (B2,
`arityFoldRealPushoutCongruence`: the real-law analogue of `arityFoldPushoutCongruence`, `ofRelation` = B1, every
other field the shipped UNCONDITIONAL `pushoutArityFoldConvSound`), the composed decision (B3,
`crossPairRealPushoutNonConv`: the interleaving pair is separated over the REAL `MonadLawRelReconstructed`
relation, hypothesis-free — LIFTING r8's empty-component `crossPairPushoutNonConvUnconditional`), and the isTrue
soundness whisker-lift (B2, `sInterleavedAssocLawConv` / `sInterleavedLeftUnitLawConv`: a REAL monad law fired
inside an `s`-interleaved word `s · (law) · …`, via the shipped `pushoutPreservesConvRight`).  Both verdict shapes
LIVE over the REAL law relation — the categorical Nelson-Oppen SOUNDNESS.  `= true`. -/
def fxAmalg_hasRealLawPushoutSoundness : Bool := true

/-- **Honesty marker — the real-law COMPLETENESS (the total two-sided decider) STAYS WALLED.**  `= true` (the wall
is honestly held).  This round ships the SOUNDNESS half only: the separating verdict is TOTAL and unconditional
over real laws (`crossPairRealPushoutNonConv`), and the convertible verdict is WITNESSED on real interleaved firings
(`sInterleavedAssocLawConv`).  It does NOT ship a total two-sided `Decidable` for ARBITRARY pushout pairs: the
`isTrue` completeness for an arbitrary convertible pair (equal semantic fold ⟹ pushout-convertible) needs a pushout
NORMAL FORM weaving the monad Eilenberg-Zilber NF through the involution `s`-whisker contexts, and the monad
unit/mult WIRE-CREATING generators break the convex-block projection (`DispatchSaturated.lean` residual (iii)).  So
`fxAmalg_hasFullSaturatedPushoutDispatch` (`DispatchSaturated.lean`) and `fxAmalg_hasGeneralPushoutDispatch`
(`PushoutBundle.lean`) STAY `false` — untouched; #2043 remains OPEN with its wall NARROWED to reverse-completeness /
pushout NF alone (r3 / WP-AMALG-3 territory).  Named node: the pushout normal form.  No fabricated flip. -/
def fxAmalg_realLawCompletenessStaysWalled : Bool := true

end FX1Poly.Polygraph.Amalgam
