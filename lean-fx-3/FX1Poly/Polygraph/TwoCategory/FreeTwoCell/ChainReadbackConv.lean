import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineChainBuilder
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.WhiskerReframing

/-! # ChainReadbackConv — the chain of a cell's spine reads back CONVERTIBLE to the cell

The equational half of chain existence: every free 2-cell is `TwoCellConvFull`-convertible to
the total readback of its own spine chain — `FramedSpineChain` is a genuine section of the
conversion quotient.

★ HONESTY — the relation is the COMPLETED convertibility `TwoCellConvFull`, NOT the bare
`TwoCellConv`: the readback's per-atom frames wrap identity-1-cell whiskers that no
`TwoCellStep` strips (the machine-checked `FreeTwoCellRealizedChain` obstruction), so the bare
statement is FALSE; the Full relation's `whiskerLeftUnit` / `whiskerRightUnit` /
`whiskerLeftComp` / `whiskerRightComp` / `whiskerExchange` laws are exactly what the whisker
arms and the final identity-accumulator collapse consume.

  * `RawTwoCellExpr.vcomp_castBoundaryLeft` — a boundary cast on the LEFT factor of a vertical
    composite extrudes to the whole composite (the middle seam flips onto the right factor);
  * `whiskerLeftAbsorb_convFull` / `whiskerRightAbsorb_convFull` — the context-absorption pair:
    an inner whiskering 1-cell absorbs into the outer accumulator context (left via the
    exchange + `whiskerLeftComp`; right via `whiskerRightComp`), the cell-level face of the
    builder's re-anchoring seams;
  * ★ `RawTwoCellExpr.spineChainDiff_readback_convFull` — the generalized induction: the
    builder's chain reads back convertible to the accumulator-whiskered cell composed with the
    rest's readback;
  * ★ `RawTwoCellExpr.cellChain_readback_convFull` — the headline: every cell is convertible
    to its own spine chain's readback.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Cast extrusion through a vertical composite -/

/-- A boundary cast on the LEFT factor of a vertical composite extrudes to the whole
composite: the source seam survives, the middle seam flips onto the right factor. -/
theorem RawTwoCellExpr.vcomp_castBoundaryLeft {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath sourcePath' middlePath middlePath' targetPath :
      ModalityPath signature.graph sourceMode targetMode}
    (hsource : sourcePath = sourcePath') (hmiddle : middlePath = middlePath')
    (cellAlpha : RawTwoCellExpr signature sourcePath middlePath)
    (cellBeta : RawTwoCellExpr signature middlePath' targetPath) :
    RawTwoCellExpr.vcomp (RawTwoCellExpr.castBoundary hsource hmiddle cellAlpha) cellBeta
      = RawTwoCellExpr.castBoundary hsource rfl
          (RawTwoCellExpr.vcomp cellAlpha
            (RawTwoCellExpr.castBoundary hmiddle.symm rfl cellBeta)) := by
  cases hsource; cases hmiddle; rfl

/-! ## The context-absorption pair -/

/-- **LEFT absorption**: an inner LEFT whiskering absorbs into the outer left accumulator —
`p ◁ (r ▷ (q ◁ body)) ≈ (p ∘ q) ◁ (r ▷ body)` up to the re-anchoring cast.  The disjoint-whisker
EXCHANGE pushes `q` through the right whisker, then `whiskerLeftComp` merges it into `p`. -/
theorem whiskerLeftAbsorb_convFull {signature : ModeSignature}
    {modeA modeB modeC modeD modeE : signature.graph.Mode}
    (leftAccumulator : ModalityPath signature.graph modeA modeB)
    (oneCell : ModalityPath signature.graph modeB modeC)
    (rightAccumulator : ModalityPath signature.graph modeD modeE)
    {bodyDom bodyCod : ModalityPath signature.graph modeC modeD}
    (body : RawTwoCellExpr signature bodyDom bodyCod) :
    TwoCellConvFull signature
      (RawTwoCellExpr.whiskerLeft leftAccumulator
        (RawTwoCellExpr.whiskerRight rightAccumulator
          (RawTwoCellExpr.whiskerLeft oneCell body)))
      (RawTwoCellExpr.castBoundary
        (reassocLeftWhisker leftAccumulator oneCell bodyDom rightAccumulator)
        (reassocLeftWhisker leftAccumulator oneCell bodyCod rightAccumulator)
        (RawTwoCellExpr.whiskerLeft (composePath leftAccumulator oneCell)
          (RawTwoCellExpr.whiskerRight rightAccumulator body))) := by
  have exchangeLifted := TwoCellConvFull.whiskerLeftCongr leftAccumulator
    (TwoCellConvFull.symm
      (TwoCellConvFull.whiskerExchange oneCell rightAccumulator body))
  rw [RawTwoCellExpr.whiskerLeft_castBoundary] at exchangeLifted
  have exchangeFlipped := TwoCellConvFull.ofCastLeft _ _ exchangeLifted
  have compFlipped := TwoCellConvFull.ofCastLeft _ _
    (TwoCellConvFull.symm (TwoCellConvFull.whiskerLeftComp leftAccumulator oneCell
      (RawTwoCellExpr.whiskerRight rightAccumulator body)))
  have compLifted := TwoCellConvFull.castBoundaryCongr
    (congrArg (composePath leftAccumulator)
      (composePath_assoc oneCell bodyDom rightAccumulator)).symm
    (congrArg (composePath leftAccumulator)
      (composePath_assoc oneCell bodyCod rightAccumulator)).symm
    compFlipped
  have combined := exchangeFlipped.trans compLifted
  rw [RawTwoCellExpr.castBoundary_castBoundary] at combined
  exact combined

/-- **RIGHT absorption**: an inner RIGHT whiskering absorbs into the outer right accumulator —
`p ◁ (r ▷ (body ▷ q)) ≈ p ◁ ((q ∘ r) ▷ body)` up to the re-anchoring cast, by
`whiskerRightComp` under the left context. -/
theorem whiskerRightAbsorb_convFull {signature : ModeSignature}
    {modeA modeB modeC modeD modeE : signature.graph.Mode}
    (leftAccumulator : ModalityPath signature.graph modeA modeB)
    {bodyDom bodyCod : ModalityPath signature.graph modeB modeC}
    (oneCell : ModalityPath signature.graph modeC modeD)
    (rightAccumulator : ModalityPath signature.graph modeD modeE)
    (body : RawTwoCellExpr signature bodyDom bodyCod) :
    TwoCellConvFull signature
      (RawTwoCellExpr.whiskerLeft leftAccumulator
        (RawTwoCellExpr.whiskerRight rightAccumulator
          (RawTwoCellExpr.whiskerRight oneCell body)))
      (RawTwoCellExpr.castBoundary
        (reassocRightWhisker leftAccumulator bodyDom oneCell rightAccumulator)
        (reassocRightWhisker leftAccumulator bodyCod oneCell rightAccumulator)
        (RawTwoCellExpr.whiskerLeft leftAccumulator
          (RawTwoCellExpr.whiskerRight (composePath oneCell rightAccumulator) body))) := by
  have compLifted := TwoCellConvFull.whiskerLeftCongr leftAccumulator
    (TwoCellConvFull.symm
      (TwoCellConvFull.whiskerRightComp oneCell rightAccumulator body))
  rw [RawTwoCellExpr.whiskerLeft_castBoundary] at compLifted
  exact TwoCellConvFull.ofCastLeft _ _ compLifted

/-! ## The generalized readback conversion -/

/-- ★ **The generalized readback conversion** — the builder's chain reads back convertible to
the accumulator-whiskered cell vertically composed with the rest's readback.  Structural
induction mirroring `spineChainDiff`: `gen` is reflexivity (both sides are the cons frame on
the rest); `id` collapses the identity frame by the whisker-identity laws + `vcompIdLeft`;
`vcomp` chains the two inductive hypotheses against the whisker-distribution laws +
`vcompAssoc`; the whisker arms transport the inductive hypothesis through the re-anchoring
casts and close with the context-absorption pair. -/
theorem RawTwoCellExpr.spineChainDiff_readback_convFull {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {localSource localTarget : signature.graph.Mode} →
    (leftAccumulator : ModalityPath signature.graph overallSource localSource) →
    (rightAccumulator : ModalityPath signature.graph localTarget overallTarget) →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    {restTarget : ModalityPath signature.graph overallSource overallTarget} →
    {restAtoms : List (SpineAtom signature overallSource overallTarget)} →
    (restChain : FramedSpineChain signature
      (composePath leftAccumulator (composePath localCod rightAccumulator))
      restTarget restAtoms) →
    TwoCellConvFull signature
      (cell.spineChainDiff leftAccumulator rightAccumulator restChain).readback
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerLeft leftAccumulator
          (RawTwoCellExpr.whiskerRight rightAccumulator cell))
        restChain.readback)
  | _, _, _, _, _, _, .gen _, _, _, _ => TwoCellConvFull.refl _
  | _, _, leftAccumulator, rightAccumulator, _, _, .id boundaryPath, _, _, restChain =>
      TwoCellConvFull.symm (TwoCellConvFull.ofConv
        (TwoCellConv.trans
          (TwoCellConv.ofStep (TwoCellStep.vcompCongrLeft restChain.readback
            (TwoCellStep.whiskerLeftCongr leftAccumulator
              (TwoCellStep.whiskerRightId boundaryPath rightAccumulator))))
          (TwoCellConv.trans
            (TwoCellConv.ofStep (TwoCellStep.vcompCongrLeft restChain.readback
              (TwoCellStep.whiskerLeftId leftAccumulator
                (composePath boundaryPath rightAccumulator))))
            (TwoCellConv.ofStep (TwoCellStep.vcompIdLeft restChain.readback)))))
  | _, _, leftAccumulator, rightAccumulator, _, _, .vcomp cellAlpha cellBeta, _, _, restChain =>
      TwoCellConvFull.trans
        (TwoCellConvFull.trans
          (RawTwoCellExpr.spineChainDiff_readback_convFull leftAccumulator rightAccumulator
            cellAlpha (cellBeta.spineChainDiff leftAccumulator rightAccumulator restChain))
          (TwoCellConvFull.vcompCongrRight
            (RawTwoCellExpr.whiskerLeft leftAccumulator
              (RawTwoCellExpr.whiskerRight rightAccumulator cellAlpha))
            (RawTwoCellExpr.spineChainDiff_readback_convFull leftAccumulator rightAccumulator
              cellBeta restChain)))
        (TwoCellConvFull.symm (TwoCellConvFull.ofConv
          (TwoCellConv.trans
            (TwoCellConv.ofStep (TwoCellStep.vcompCongrLeft restChain.readback
              (TwoCellStep.whiskerLeftCongr leftAccumulator
                (TwoCellStep.whiskerRightVcomp rightAccumulator cellAlpha cellBeta))))
            (TwoCellConv.trans
              (TwoCellConv.ofStep (TwoCellStep.vcompCongrLeft restChain.readback
                (TwoCellStep.whiskerLeftVcomp leftAccumulator
                  (RawTwoCellExpr.whiskerRight rightAccumulator cellAlpha)
                  (RawTwoCellExpr.whiskerRight rightAccumulator cellBeta))))
              (TwoCellConv.ofStep (TwoCellStep.vcompAssoc
                (RawTwoCellExpr.whiskerLeft leftAccumulator
                  (RawTwoCellExpr.whiskerRight rightAccumulator cellAlpha))
                (RawTwoCellExpr.whiskerLeft leftAccumulator
                  (RawTwoCellExpr.whiskerRight rightAccumulator cellBeta))
                restChain.readback))))))
  | _, _, leftAccumulator, rightAccumulator, _, _, .whiskerLeft oneCell body, _, _, restChain => by
      show TwoCellConvFull signature
        ((FramedSpineChain.castSource _
          (body.spineChainDiff (composePath leftAccumulator oneCell) rightAccumulator
            (restChain.castSource _))).readback) _
      rw [FramedSpineChain.castSource_readback]
      have innerConv := RawTwoCellExpr.spineChainDiff_readback_convFull
        (composePath leftAccumulator oneCell) rightAccumulator body
        (restChain.castSource
          (reassocLeftWhisker leftAccumulator oneCell _ rightAccumulator).symm)
      rw [FramedSpineChain.castSource_readback] at innerConv
      have transported := TwoCellConvFull.castBoundaryCongr
        (reassocLeftWhisker leftAccumulator oneCell _ rightAccumulator) rfl innerConv
      have splitLeg := TwoCellConvFull.vcompCongrLeft restChain.readback
        (whiskerLeftAbsorb_convFull leftAccumulator oneCell rightAccumulator body)
      rw [RawTwoCellExpr.vcomp_castBoundaryLeft] at splitLeg
      exact transported.trans splitLeg.symm
  | _, _, leftAccumulator, rightAccumulator, _, _, .whiskerRight oneCell body, _, _, restChain => by
      show TwoCellConvFull signature
        ((FramedSpineChain.castSource _
          (body.spineChainDiff leftAccumulator (composePath oneCell rightAccumulator)
            (restChain.castSource _))).readback) _
      rw [FramedSpineChain.castSource_readback]
      have innerConv := RawTwoCellExpr.spineChainDiff_readback_convFull
        leftAccumulator (composePath oneCell rightAccumulator) body
        (restChain.castSource
          (reassocRightWhisker leftAccumulator _ oneCell rightAccumulator).symm)
      rw [FramedSpineChain.castSource_readback] at innerConv
      have transported := TwoCellConvFull.castBoundaryCongr
        (reassocRightWhisker leftAccumulator _ oneCell rightAccumulator) rfl innerConv
      have splitLeg := TwoCellConvFull.vcompCongrLeft restChain.readback
        (whiskerRightAbsorb_convFull leftAccumulator oneCell rightAccumulator body)
      rw [RawTwoCellExpr.vcomp_castBoundaryLeft] at splitLeg
      exact transported.trans splitLeg.symm

/-! ## The headline: the cell converts to its own spine chain's readback -/

/-- ★ **Chain existence, equational half**: every free 2-cell is `TwoCellConvFull`-convertible
to the total readback of its own spine chain — `FramedSpineChain` is a genuine section of the
conversion quotient.  The generalized conversion at identity accumulators, with the
identity-frame collapse (`vcompIdRight`, the whisker-unit laws) transported through the
boundary casts. -/
theorem RawTwoCellExpr.cellChain_readback_convFull {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    TwoCellConvFull signature cell cell.cellChain.readback := by
  show TwoCellConvFull signature cell
    ((FramedSpineChain.castTarget _ (FramedSpineChain.castSource _
      (cell.spineChainDiff (identityPath sourceMode) (identityPath targetMode)
        (FramedSpineChain.nil
          (composePath targetPath (identityPath targetMode)))))).readback)
  rw [FramedSpineChain.castTarget_readback, FramedSpineChain.castSource_readback,
    RawTwoCellExpr.castBoundary_castBoundary]
  have mainConv := TwoCellConvFull.castBoundaryCongr
    ((composePath_identityPath_right sourcePath).trans rfl)
    ((rfl : composePath targetPath (identityPath targetMode) = _).trans
      (composePath_identityPath_right targetPath))
    (RawTwoCellExpr.spineChainDiff_readback_convFull
      (identityPath sourceMode) (identityPath targetMode) cell
      (FramedSpineChain.nil (composePath targetPath (identityPath targetMode))))
  have stripLeg := TwoCellConvFull.castBoundaryCongr
    ((composePath_identityPath_right sourcePath).trans rfl)
    ((rfl : composePath targetPath (identityPath targetMode) = _).trans
      (composePath_identityPath_right targetPath))
    (TwoCellConvFull.trans
      (TwoCellConvFull.ofConv (TwoCellConv.ofStep (TwoCellStep.vcompIdRight
        (RawTwoCellExpr.whiskerLeft (identityPath sourceMode)
          (RawTwoCellExpr.whiskerRight (identityPath targetMode) cell)))))
      (TwoCellConvFull.trans
        (TwoCellConvFull.whiskerLeftUnit
          (RawTwoCellExpr.whiskerRight (identityPath targetMode) cell))
        (TwoCellConvFull.whiskerRightUnit cell)))
  rw [RawTwoCellExpr.castBoundary_castBoundary] at stripLeg
  exact (TwoCellConvFull.trans mainConv stripLeg).symm

/-! ## Honesty marker -/

/-- **Honesty marker — chain existence is COMPLETE (both halves).**  Every free 2-cell's spine
is chained (`cellChain`) and the chain reads back CONVERTIBLE to the cell
(`cellChain_readback_convFull`) — `FramedSpineChain` is a genuine section of the conversion
quotient.  The relation is the COMPLETED convertibility `TwoCellConvFull` (the bare
`TwoCellConv` statement is FALSE by the machine-checked identity-whisker obstruction of
`FreeTwoCellRealizedChain`; the Full whisker-functoriality laws are exactly the fix).
Downstream: the Godement step lifted onto chains and the generic trace reconstruction should
be stated over `TwoCellConvFull` accordingly.  `= true`. -/
def fxMode_hasChainReadbackConv : Bool := true

end FX1Poly.Polygraph
