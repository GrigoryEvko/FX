import FX1Poly.Polygraph.TwoCategory.Amalgam.ConvFullFunctorDispatch
import FX1Poly.Polygraph.TwoCategory.Amalgam.ComposableFragmentDispatch
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutMonotoneReflection

/-! # Polygraph/TwoCategory/Amalgam/Modularity — the modularity theorem (conv-in-pushout iff free, disjoint scope)
+ the cross-block commutation leg (WP-AMALG-2 r1, B2)

The dispatch's correctness principle: over the DISJOINT scope (no crossing law — both component law relations
provably empty), a 2-cell convertibility in the pushout `comp1 +_M comp2` is decided BLOCKWISE, i.e. it coincides
with the FREE pushout word problem `TwoCellConvFull`.  This is the 2-categorical instance of Toyama's modularity of
confluence for the disjoint union (Toyama 1987): the amalgam's word problem IS the free coproduct word problem when
no law crosses the boundary.  This file assembles that biconditional from the two shipped halves and records the
cross-block Godement commutation as its named leg.

## The two halves, assembled

  * **SOUNDNESS (blockwise ⟹ pushout)** — a component convertibility lifts, along the coprojection cell functor
    `mapCellAlong`, to a pushout convertibility (`ConvFullFunctorDispatch.pushoutPreservesConvLeft` /
    `pushoutPreservesConvRight`, UNCONDITIONAL).  A component-block decision embeds into the amalgam.
  * **COMPLETENESS (pushout ⟹ free)** — over a provably-empty pushout law relation
    (`ComposableFragmentDispatch.saturatedConvOverPushoutRows_empty`, from both component relations empty), the
    pushout saturated convertibility reflects EXACTLY to the free `TwoCellConvFull`
    (`saturatedConvOverEmptyRows_iff_full`).  `ofRelation` is the sole conservativity boundary — a genuine crossing
    law would break exactly here (the walled real-law case).

Together: `SaturatedConvOver pushout (SaturatedConvOverPushout …) ↔ TwoCellConvFull pushout`.  Since for empty
component laws the coprojected component blocks are themselves free-convertible, "iff free" IS the "iff blockwise"
modularity statement in the disjoint scope.

## The cross-block commutation leg (FREE — the recon's finding)

The one cross-component interaction the dispatch needs — two whiskerings in DIFFERENT components at DISJOINT boundary
positions commute — is `DispatchSaturated.crossComponentWhiskerCommute`, discharged by a SINGLE constructor
`ofFull (whiskerExchange …)` (the Godement / middle-four-exchange law).  It adds NO obligation.  This file records a
fresh concrete instance (`modularityCrossBlockCommute`, `s` in component 1, `t` in component 2, identity body) over
the REAL `involution +_M monad` base relation as the named modularity leg.

## The disjoint-scope caveat (recorded, not hidden)

The forward (completeness) direction holds ONLY for the empty-crossing-law scope; a component contributing genuine
fireable laws breaks the `ofRelation` conservativity boundary (the walled Baader-Tinelli shared-symbol case,
`fxAmalg_hasFullSaturatedPushoutDispatch = false`).  The marker below scopes the biconditional honestly.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The modularity biconditional (general, disjoint scope) -/

/-- ★ **The MODULARITY THEOREM (disjoint scope).**  Over the pushout `comp1 +_M comp2` with both component law
relations provably empty (the disjoint / no-crossing-law scope), the pushout saturated convertibility at the base
relation `SaturatedConvOverPushout` coincides with the FREE pushout word problem `TwoCellConvFull`.  The completeness
half is `saturatedConvOverEmptyRows_iff_full` applied to the pushout emptiness `saturatedConvOverPushoutRows_empty`;
the soundness embedding is `SaturatedConvOver.ofFull`.  This is Toyama's confluence-modularity for the disjoint union,
2-categorically: the amalgam's word problem IS the free coproduct word problem when no law crosses the boundary. -/
theorem pushoutConvIffFree_ofEmptyComponents {comp1 comp2 : ModeComputad}
    (sameModes : comp1.modeCount = comp2.modeCount)
    (inclLeft : ComputadMorphismTwo comp1 (pushoutShared comp1 comp2 sameModes))
    (inclRight : ComputadMorphismTwo comp2 (pushoutShared comp1 comp2 sameModes))
    {baseRel1 : CellRel comp1.toModeSignature} {baseRel2 : CellRel comp2.toModeSignature}
    (rows1Empty : {sourceMode targetMode : comp1.toModeSignature.graph.Mode} →
      {sourcePath targetPath : ModalityPath comp1.toModeSignature.graph sourceMode targetMode} →
      {cellAlpha cellBeta : RawTwoCellExpr comp1.toModeSignature sourcePath targetPath} →
      baseRel1 cellAlpha cellBeta → False)
    (rows2Empty : {sourceMode targetMode : comp2.toModeSignature.graph.Mode} →
      {sourcePath targetPath : ModalityPath comp2.toModeSignature.graph sourceMode targetMode} →
      {cellAlpha cellBeta : RawTwoCellExpr comp2.toModeSignature sourcePath targetPath} →
      baseRel2 cellAlpha cellBeta → False)
    {sourceMode targetMode : (pushoutShared comp1 comp2 sameModes).toModeSignature.graph.Mode}
    {sourcePath targetPath :
      ModalityPath (pushoutShared comp1 comp2 sameModes).toModeSignature.graph sourceMode targetMode}
    (cellAlpha cellBeta : RawTwoCellExpr (pushoutShared comp1 comp2 sameModes).toModeSignature sourcePath targetPath) :
    SaturatedConvOver (pushoutShared comp1 comp2 sameModes).toModeSignature
        (SaturatedConvOverPushout comp1 comp2 sameModes inclLeft inclRight baseRel1 baseRel2) cellAlpha cellBeta
      ↔ TwoCellConvFull (pushoutShared comp1 comp2 sameModes).toModeSignature cellAlpha cellBeta :=
  saturatedConvOverEmptyRows_iff_full
    (fun row => saturatedConvOverPushoutRows_empty rows1Empty rows2Empty row) cellAlpha cellBeta

/-! ## The concrete instance at the `involution +_M monad` pushout -/

/-- ★ **The modularity biconditional at `involution +_M monad`.**  Over the real witness pushout (real right
coprojection `inclusionRightTwoReal`, empty component laws), the pushout saturated convertibility at
`crossPairPushoutRel` coincides with the free `TwoCellConvFull`.  This is exactly the reflection the shipped combined
decider (`involutionMonadEmptyRowsDispatch`) computes on the interleaving pair — now as a biconditional over ALL
parallel pairs. -/
theorem involutionMonadPushoutConvIffFree
    {sourceMode targetMode : involutionMonadPushout.toModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath involutionMonadPushout.toModeSignature.graph sourceMode targetMode}
    (cellAlpha cellBeta : RawTwoCellExpr involutionMonadPushout.toModeSignature sourcePath targetPath) :
    SaturatedConvOver involutionMonadPushout.toModeSignature crossPairPushoutRel cellAlpha cellBeta
      ↔ TwoCellConvFull involutionMonadPushout.toModeSignature cellAlpha cellBeta :=
  pushoutConvIffFree_ofEmptyComponents involutionMonadSameModes
    (inclusionLeftTwo involutionComputad monadComputad involutionMonadSameModes rfl)
    (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes)
    (fun row => row.elim) (fun row => row.elim) cellAlpha cellBeta

/-! ## Soundness leg: a component (blockwise) convertibility lifts into the pushout -/

/-- ★ **Blockwise soundness, non-vacuously** — a GENUINE (non-reflexive) monad-component convertibility, the unit
whisker law `id ◁ eta ≈ eta`, lifts along the real right coprojection to a pushout convertibility of the
`mapCellAlong`-images (via `pushoutPreservesConvRight`, UNCONDITIONAL).  A component-block decision embedding into
the amalgam — the "blockwise ⟹ pushout" direction on a real law, not just reflexivity. -/
def modularityRightBlockLift :=
  pushoutPreservesConvRight involutionMonadSameModes
    (inclusionLeftTwo involutionComputad monadComputad involutionMonadSameModes rfl)
    (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes)
    (emptyCellRel involutionComputad.toModeSignature)
    (emptyCellRel monadComputad.toModeSignature)
    (SaturatedConvOver.ofFull
      (TwoCellConvFull.whiskerLeftUnit
        (RawTwoCellExpr.gen (signature := monadComputad.toModeSignature) monadComputadReconstructsUnit)))

/-! ## The cross-block commutation leg (FREE) -/

/-- ★ **The cross-block Godement commutation leg** — a fresh concrete instance of `crossComponentWhiskerCommute`
over the REAL `involution +_M monad` base relation: the `s`-left-whisker of a `t`-right-whisker of the identity
body is saturated-convertible to the reversed order (up to the associativity cast).  GENUINELY different-component
whiskers (`s` in component 1, `t` in component 2), discharged FREE by one `ofFull (whiskerExchange …)`.  The one
cross-component interaction the modularity theorem needs, adding no obligation. -/
def modularityCrossBlockCommute :=
  crossComponentWhiskerCommute (baseRel := crossPairPushoutRel)
    monadPushSPath monadPushTPath
    (RawTwoCellExpr.id (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode))

/-! ## Honesty marker -/

/-- ★ **Honesty marker — the MODULARITY THEOREM ships in the disjoint scope (B2).**  The general biconditional
`pushoutConvIffFree_ofEmptyComponents` (pushout saturated convertibility over `SaturatedConvOverPushout` with empty
component laws ↔ free `TwoCellConvFull`), assembled from the UNCONDITIONAL soundness lift
(`pushoutPreservesConvLeft` / `pushoutPreservesConvRight`) and the empty-law completeness
(`saturatedConvOverEmptyRows_iff_full` ∘ `saturatedConvOverPushoutRows_empty`); the concrete instance
`involutionMonadPushoutConvIffFree`; a non-vacuous blockwise soundness lift of a real monad law
(`modularityRightBlockLift`); and the cross-block Godement commutation leg (`modularityCrossBlockCommute`, FREE).
This is Toyama's confluence-modularity for the disjoint union, 2-categorically.  The DISJOINT-SCOPE caveat is
load-bearing and recorded: the completeness direction holds only for empty crossing laws — a genuine crossing law
breaks the `ofRelation` conservativity boundary (`fxAmalg_hasFullSaturatedPushoutDispatch = false`, the walled
Baader-Tinelli shared-symbol case).  `= true`. -/
def fxAmalg_hasModularityDisjointScope : Bool := true

end FX1Poly.Polygraph.Amalgam
