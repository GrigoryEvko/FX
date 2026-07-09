import FX1Poly.Polygraph.TwoCategory.Amalgam.ConvFullFunctor
import FX1Poly.Polygraph.TwoCategory.Amalgam.DispatchSaturated

/-! # Polygraph/TwoCategory/Amalgam/ConvFullFunctorDispatch — the UNCONDITIONAL saturated-conv soundness lift
(WP-AMALG r5, P1 wiring)

`DispatchSaturated.lean` (r4) reduced the saturated-conv soundness lift `mapCellAlong_preservesConv` to a single
hypothesis `fullPreserved` — the STRUCTURAL FUNCTORIALITY of `mapCellAlong` for the completed convertibility
`TwoCellConvFull`.  `ConvFullFunctor.lean` (r5) DISCHARGED it (`mapTwoCellConvFull`).  This file wires the two
together: `mapCellAlong_preservesConvUnconditional` instantiates `fullPreserved := mapTwoCellConvFull`, dropping
the hypothesis.  The r4 conditional master `mapCellAlong_preservesConv` stays untouched for compatibility.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-- ★ **The UNCONDITIONAL saturated-conv soundness lift** — a component saturated convertibility transports to a
pushout saturated convertibility of the `mapCellAlong`-images, needing ONLY the base-row map `rowMap` (discharged
by construction of `SaturatedConvOverPushout`); the structural-functoriality hypothesis of the r4 conditional
`mapCellAlong_preservesConv` is now supplied by `mapTwoCellConvFull`.  This is the SOUNDNESS direction of the
saturated dispatch, no longer conditional. -/
theorem mapCellAlong_preservesConvUnconditional {source target : ModeComputad}
    (morphism : ComputadMorphismTwo source target)
    {baseRelSrc : CellRel source.toModeSignature} {baseRelTgt : CellRel target.toModeSignature}
    (rowMap : {sourceMode targetMode : Fin source.modeCount} →
      {sourcePath targetPath : ModalityPath source.toModeGraph sourceMode targetMode} →
      {cellA cellB : RawTwoCellExpr source.toModeSignature sourcePath targetPath} →
      baseRelSrc cellA cellB →
      baseRelTgt (mapCellAlong morphism cellA) (mapCellAlong morphism cellB))
    {sourceMode targetMode : Fin source.modeCount}
    {sourcePath targetPath : ModalityPath source.toModeGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr source.toModeSignature sourcePath targetPath}
    (conv : SaturatedConvOver source.toModeSignature baseRelSrc cellAlpha cellBeta) :
    SaturatedConvOver target.toModeSignature baseRelTgt
      (mapCellAlong morphism cellAlpha) (mapCellAlong morphism cellBeta) :=
  mapCellAlong_preservesConv morphism (fun convFull => mapTwoCellConvFull morphism convFull) rowMap conv

/-- ★ **The pushout saturated-conv soundness, both coprojections, UNCONDITIONALLY.**  A component-1 saturated
convertibility lifts to the pushout saturated convertibility over `SaturatedConvOverPushout` — the `left`
constructor supplies the `rowMap`.  No structural-functoriality hypothesis (it is `mapTwoCellConvFull`).  The
right-component dual is `pushoutPreservesConvRight`. -/
theorem pushoutPreservesConvLeft {comp1 comp2 : ModeComputad}
    (sameModes : comp1.modeCount = comp2.modeCount)
    (inclLeft : ComputadMorphismTwo comp1 (pushoutShared comp1 comp2 sameModes))
    (inclRight : ComputadMorphismTwo comp2 (pushoutShared comp1 comp2 sameModes))
    (baseRel1 : CellRel comp1.toModeSignature) (baseRel2 : CellRel comp2.toModeSignature)
    {sourceMode targetMode : Fin comp1.modeCount}
    {sourcePath targetPath : ModalityPath comp1.toModeGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr comp1.toModeSignature sourcePath targetPath}
    (conv : SaturatedConvOver comp1.toModeSignature baseRel1 cellAlpha cellBeta) :
    SaturatedConvOver (pushoutShared comp1 comp2 sameModes).toModeSignature
      (SaturatedConvOverPushout comp1 comp2 sameModes inclLeft inclRight baseRel1 baseRel2)
      (mapCellAlong inclLeft cellAlpha) (mapCellAlong inclLeft cellBeta) :=
  mapCellAlong_preservesConvUnconditional inclLeft
    (fun row => SaturatedConvOverPushout.left row) conv

/-- The right-component dual of `pushoutPreservesConvLeft`. -/
theorem pushoutPreservesConvRight {comp1 comp2 : ModeComputad}
    (sameModes : comp1.modeCount = comp2.modeCount)
    (inclLeft : ComputadMorphismTwo comp1 (pushoutShared comp1 comp2 sameModes))
    (inclRight : ComputadMorphismTwo comp2 (pushoutShared comp1 comp2 sameModes))
    (baseRel1 : CellRel comp1.toModeSignature) (baseRel2 : CellRel comp2.toModeSignature)
    {sourceMode targetMode : Fin comp2.modeCount}
    {sourcePath targetPath : ModalityPath comp2.toModeGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr comp2.toModeSignature sourcePath targetPath}
    (conv : SaturatedConvOver comp2.toModeSignature baseRel2 cellAlpha cellBeta) :
    SaturatedConvOver (pushoutShared comp1 comp2 sameModes).toModeSignature
      (SaturatedConvOverPushout comp1 comp2 sameModes inclLeft inclRight baseRel1 baseRel2)
      (mapCellAlong inclRight cellAlpha) (mapCellAlong inclRight cellBeta) :=
  mapCellAlong_preservesConvUnconditional inclRight
    (fun row => SaturatedConvOverPushout.right row) conv

/-! ## Honesty marker -/

/-- ★ **Honesty marker — the saturated-conv SOUNDNESS lift is UNCONDITIONAL (r5 P1 wired).**  Both coprojections'
component convertibilities lift to the pushout `SaturatedConvOverPushout` with NO structural-functoriality
hypothesis (`pushoutPreservesConvLeft` / `pushoutPreservesConvRight`), because `mapTwoCellConvFull` supplies it.
The r4 conditional master `mapCellAlong_preservesConv` is retained (compatibility).  The FULL dispatch stays open
on the three named walls (real-generator coprojection, reconstruction faithfulness iso, purification
completeness) — the commutation and the soundness functoriality are BOTH now closed.  `= true`. -/
def fxAmalg_hasUnconditionalSoundnessLift : Bool := true

end FX1Poly.Polygraph.Amalgam
