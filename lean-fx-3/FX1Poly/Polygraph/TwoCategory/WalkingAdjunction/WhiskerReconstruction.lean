import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.WhiskerFunctoriality
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.RealizedChain
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.WhiskerReframing

/-! # mode-3 floor — the YES-direction reconstruction over the COMPLETED convertibility (sharpened residual)

`FreeTwoCellWhiskerFunctoriality` shipped `TwoCellConvFull` — the completed free-strict-2-category convertibility
(`TwoCellConv` + whisker FUNCTORIALITY + congruence closure) — and its spine SOUNDNESS (the NO-direction).
`FreeTwoCellSpineReadback` / `FreeTwoCellRealizedChain` reduced the seed's full `TwoCellConv` decision to
`(traceDecision, nfReconstruct)` and then RELOCATED `nfReconstruct`'s obstruction: the spine→cell readback is
UNSOUND on `TwoCellConv` because the per-atom `atomFrame` wraps identity-1-cell whiskers that no `TwoCellStep`
strips (machine-checked: `atomFrame` of the unit's spine atom has the SAME spine as the bare `gen unit` but a
DISTINCT interchange-free normal form).

This file uses whisker functoriality to **dissolve that obstruction over `TwoCellConvFull`** and to assemble the
YES-direction architecture, leaving a strictly-sharpened residual.

## What this file ships (each piece zero-axiom)

  ★ `adjunctionUnitFrame_convFull_unit` — the **obstruction removal**: the per-atom readback
    `atomFrame adjunctionUnitSpineAtom` (= `nil ◁ (nil ▷ gen unit)`), which `FreeTwoCellRealizedChain` proved has
    a DISTINCT interchange-free normal form from the bare unit (`adjunctionUnitFrame_normalForm_ne_unit`), is now
    `TwoCellConvFull` to the bare unit (up to the boundary cast): `whiskerLeftUnit` strips the identity LEFT
    whisker, `whiskerRightUnit` strips the identity RIGHT whisker.  This is the precise, machine-checked
    statement that whisker functoriality makes the readback SOUND where it was unsound on `TwoCellConv` — the same
    cells the prior pass exhibited as the obstruction are now convertible.
  ★ `convToInterchangeFreeNormalFormFull` — every cell is `TwoCellConvFull` to its interchange-free normal form
    (`convToInterchangeFreeNormalForm` lifted through `ofConv`).
  ★ `chainToCellConcatConvFull` — the boundary-coherent chain readback is a monoid homomorphism up to
    `TwoCellConvFull` (`chainToCell_concat` lifted): reassembling a concatenated chain is `TwoCellConvFull` to the
    vertical composite of the reassemblies — the structure the trace equivalence acts on, now over the completed
    convertibility.
  ★ `AdjunctionSpineTraceReconstructionFull` / `AdjunctionNfTraceReconstructionFull` — the YES-direction
    obligations restated over `TwoCellConvFull`.
  ★ `adjunctionReconstructionFromNfFull` — the **reduction** (mirroring `adjunctionReconstructionFromNf`, now over
    the SOUND relation): the full reconstruction follows from its normal-form restriction.  `cellFirst ≈ nf
    cellFirst`, `nf cellSecond ≈ cellSecond` (the lift above), and `interchangeFreeNormalForm_spine_eq` transports
    the trace equivalence onto the normal forms.  So the YES-direction is owed ONLY for two interchange-free
    normal forms.

## What is DEFERRED — the precise, sharpened residual (gate stays `false`)

The residual is `AdjunctionNfTraceReconstructionFull`: realize a `SpineTraceEquiv` between two interchange-free
NORMAL forms' spines as a cell-level `TwoCellConvFull`.  The honest remaining development is the
**boundary-coherent canonical-chain readback bridge** the route needs:

  * a `cellConvCanonical : (a) → TwoCellConvFull a (chainToCell (canonicalChain a))`, where `canonicalChain a`
    realizes `a.spine` at `a`'s boundary — proved by induction on the cell, the `whiskerLeft`/`whiskerRight`
    cases PUSHING the whisker context into each atom via the four whisker-functoriality laws (cell-level
    distribution: `whiskerLeft o (vcomp …)` over the chain by `whiskerLeftVcomp`, then `whiskerLeft o (atomFrame
    a)` into `atomFrame (whiskered a)` by `whiskerLeftComp`).  Whisker functoriality makes every step convertible;
    what is left to build is the `whiskerLeftChain` / `whiskerRightChain` chain TRANSFORMS, whose `cons` indices
    shift by `composePath` ASSOCIATIVITY — so they need the coherence-refined chain carrying its inter-atom
    boundary equalities (the development `FreeTwoCellRealizedChain`'s header names).  `castBoundary` + `Eq`
    proof-irrelevance handle the per-step casts; the chain-index coherence is the genuine remaining work.
  * the trace lift `SpineTraceEquiv → TwoCellConvFull` through `chainToCell`: the `godement` case is
    `framedGodementInterchangeConv` / `godementWithTailConv` (already `TwoCellConv`, lifted by `ofConv`); the
    `consCongr` case is `TwoCellConvFull.vcompCongrRight`; assembled along the readback of the (decomposed) chain.

With those, `adjunctionReconstructionFromNfFull` closes the full YES-direction; the parent then combines
`nfReconstructFull` with the list-level `traceDecision` and the soundness NO-branch into
`Decidable (TwoCellConvFull …)`.  Until then `fxMode_hasModeRelativeConvDecision` /
`fxMode_hasDecidableTwoCellEquality` stay `false`.

Raw Lean 4 + Init; every shipped declaration `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-
free (the lifts are `ofConv`; the reduction is `rw` on the spine-preservation equalities then `TwoCellConvFull`
transitivity; the obstruction removal is two whisker-unit laws and `trans`).  Per-declaration `#assert_no_axioms`
gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The obstruction, dissolved over the completed convertibility -/

/-- ★ **The readback obstruction, dissolved.**  `FreeTwoCellRealizedChain` proved the per-atom readback
`atomFrame adjunctionUnitSpineAtom` (= `nil ◁ (nil ▷ gen unit)`) has the SAME spine as the bare `gen unit`
(`adjunctionUnitFrame_spine_eq_unit`) yet a DISTINCT interchange-free normal form
(`adjunctionUnitFrame_normalForm_ne_unit`) — the precise obstruction to the spine→cell reconstruction on
`TwoCellConv`.  Over the COMPLETED convertibility it dissolves: `atomFrame adjunctionUnitSpineAtom` is
`TwoCellConvFull` to the bare unit (up to the boundary cast), by stripping the identity LEFT whisker
(`whiskerLeftUnit`) then the identity RIGHT whisker (`whiskerRightUnit`).  The same spine-equal,
normal-form-distinct cells the prior pass isolated as unsound are now convertible — whisker functoriality is
exactly what the reconstruction's soundness needed. -/
theorem adjunctionUnitFrame_convFull_unit :
    TwoCellConvFull adjunctionModeSignature
      (atomFrame adjunctionUnitSpineAtom)
      (RawTwoCellExpr.castBoundary
        (composePath_identityPath_right
          (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)).symm
        (composePath_identityPath_right adjunctionLeftThenRight).symm
        adjunctionUnitTwoCell) :=
  TwoCellConvFull.trans
    (TwoCellConvFull.whiskerLeftUnit
      (RawTwoCellExpr.whiskerRight adjunctionUnitSpineAtom.rightContext
        (RawTwoCellExpr.gen adjunctionUnitSpineAtom.generator)))
    (TwoCellConvFull.whiskerRightUnit adjunctionUnitTwoCell)

/-! ## The cell↔normal-form bridge + readback homomorphism, over the completed convertibility -/

/-- Every cell is `TwoCellConvFull` to its interchange-free normal form (`convToInterchangeFreeNormalForm` lifted
through `ofConv` — the completed relation contains the interchange-free reduction). -/
theorem convToInterchangeFreeNormalFormFull {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    TwoCellConvFull signature cell (nfCell cell) :=
  TwoCellConvFull.ofConv (convToInterchangeFreeNormalForm cell)

/-- The boundary-coherent chain readback is a **monoid homomorphism up to `TwoCellConvFull`**
(`chainToCell_concat` lifted): reassembling a concatenated chain is `TwoCellConvFull` to the vertical composite of
the two reassemblies.  The readback respects the structure the trace equivalence acts on, now over the completed
convertibility — an ingredient of the deferred trace lift. -/
theorem chainToCellConcatConvFull {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {sourcePath middlePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (firstChain : RealizedSpineChain signature sourcePath middlePath)
    (secondChain : RealizedSpineChain signature middlePath targetPath) :
    TwoCellConvFull signature (chainToCell (concatRealizedChain firstChain secondChain))
      (RawTwoCellExpr.vcomp (chainToCell firstChain) (chainToCell secondChain)) :=
  TwoCellConvFull.ofConv (chainToCell_concat firstChain secondChain)

/-! ## The YES-direction obligations + the reduction to the normal-form restriction -/

/-- The seed's **full readback reconstruction**, over the completed convertibility: a spine-level trace
equivalence lifts to a cell-level `TwoCellConvFull` (the YES-direction past the `spine` quotient, now over the
relation faithful to the free strict 2-category). -/
abbrev AdjunctionSpineTraceReconstructionFull : Prop :=
  {sourceMode targetMode : adjunctionModeSignature.graph.Mode} →
  {sourcePath targetPath : ModalityPath adjunctionModeSignature.graph sourceMode targetMode} →
  (cellFirst cellSecond : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) →
  SpineTraceEquiv adjunctionModeSignature cellFirst.spine cellSecond.spine →
  TwoCellConvFull adjunctionModeSignature cellFirst cellSecond

/-- The **normal-form-restricted** YES-direction obligation, over the completed convertibility: a trace
equivalence between two cells' interchange-free NORMAL forms' spines realized as a `TwoCellConvFull` of those
normal forms.  This is the precise, sharpened residual (see the honesty marker). -/
abbrev AdjunctionNfTraceReconstructionFull : Prop :=
  {sourceMode targetMode : adjunctionModeSignature.graph.Mode} →
  {sourcePath targetPath : ModalityPath adjunctionModeSignature.graph sourceMode targetMode} →
  (cellFirst cellSecond : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) →
  SpineTraceEquiv adjunctionModeSignature (nfCell cellFirst).spine (nfCell cellSecond).spine →
  TwoCellConvFull adjunctionModeSignature (nfCell cellFirst) (nfCell cellSecond)

/-- ★ **The reduction** (mirroring `adjunctionReconstructionFromNf`, now over the SOUND completed relation): the
full YES-direction reconstruction follows from its normal-form restriction.  The normal forms' spines agree with
the cells' (`interchangeFreeNormalForm_spine_eq`), so the trace equivalence transports onto the normal forms; the
normal-form readback then converts `nf cellFirst ≈ nf cellSecond`; and the cell↔normal-form bridge
(`convToInterchangeFreeNormalFormFull`, both sides) closes
`cellFirst ≈ nf cellFirst ≈ nf cellSecond ≈ cellSecond`.  So `AdjunctionSpineTraceReconstructionFull` is owed only
for two interchange-free normal forms. -/
theorem adjunctionReconstructionFromNfFull
    (nfReconstructFull : AdjunctionNfTraceReconstructionFull) :
    AdjunctionSpineTraceReconstructionFull := by
  intro sourceMode targetMode sourcePath targetPath cellFirst cellSecond tracesEquiv
  have spineFirst : (nfCell cellFirst).spine = cellFirst.spine :=
    interchangeFreeNormalForm_spine_eq cellFirst
  have spineSecond : (nfCell cellSecond).spine = cellSecond.spine :=
    interchangeFreeNormalForm_spine_eq cellSecond
  have tracesEquivNf : SpineTraceEquiv adjunctionModeSignature
      (nfCell cellFirst).spine (nfCell cellSecond).spine := by
    rw [spineFirst, spineSecond]; exact tracesEquiv
  exact TwoCellConvFull.trans (convToInterchangeFreeNormalFormFull cellFirst)
    (TwoCellConvFull.trans (nfReconstructFull cellFirst cellSecond tracesEquivNf)
      (TwoCellConvFull.symm (convToInterchangeFreeNormalFormFull cellSecond)))

/-! ## Honesty marker -/

/-- **Honesty marker — the whisker-functoriality reconstruction KIT is shipped.**  Everything the
per-atom whisker-context manipulation needs now exists: the obstruction is dissolved over the completed
convertibility (`adjunctionUnitFrame_convFull_unit`), the cell↔normal-form bridge and the readback
homomorphism are lifted (`convToInterchangeFreeNormalFormFull`, `chainToCellConcatConvFull`), the full
reconstruction is REDUCED to its normal-form restriction (`adjunctionReconstructionFromNfFull`), and —
the piece this marker gates — `TwoCellConvFull` hosts ALL FIVE whisker-functoriality laws (units,
composites, and the disjoint-whisker `whiskerExchange`, previously posited only at the saturated
relation) with the signature-generic atom re-framing pair (`whiskerLeft_atomFrame_convFull` /
`whiskerRight_atomFrame_convFull` in `FreeTwoCellWhiskerReframing`) converting outer whiskers of a
frame into frames of context-extended atoms.

SUPERSEDED (this reduction's NF-restricted residual is no longer the route): the general
`AdjunctionSpineTraceReconstructionFull` — hence a fortiori its NF restriction
`AdjunctionNfTraceReconstructionFull` — is now DISCHARGED DIRECTLY by the shipped free FREE-4
`RawTwoCellExpr.twoCellConvFull_ofSpineTraceEquiv` (`adjunctionSpineTraceReconstructionFull`,
`AdjunctionTwoCellConvFullTraceRoute`), so the boundary-coherent chain-whisker transforms + `chainToCell`-trace
lift (the realized-chain bridge `fxMode_hasRealizedChainCellBridge` / arc reconstruction
`fxMode_hasArcCellReconstruction`, both `false`) are a superseded alternative, not a blocker.  With the
`traceDecision` also discharged ungated (`adjunctionSpineTraceDecision`), the FAITHFUL `TwoCellConvFull` decision
at the seed is UNCONDITIONAL (`adjunctionDecideTwoCellConvFull`,
`fxMode_hasFaithfulTwoCellDecisionModuloTrace = true`).  The spine SOUNDNESS (NO-direction) is shipped in
`FreeTwoCellWhiskerFunctoriality`; the convergent-3-polygraph route stays blocked (interchange non-confluence is
real).  `fxMode_hasModeRelativeConvDecision` / `fxMode_hasDecidableTwoCellEquality` stay `false` for an
INDEPENDENT reason — the BARE `TwoCellConv` relation mismatch (its `reconstruct` provably FALSE, FREE-2), NOT
this NF residual.  `= true`. -/
def fxMode_hasWhiskerFunctorialityReconstruction : Bool := true

end FX1Poly.Polygraph
