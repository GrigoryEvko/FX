import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ChainAnchor
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineGodement

/-! # ChainGodementStep — the Godement spine step lifted onto framed chains (FREE-3)

One `SpineGodementStep` between chained atom lists is one `TwoCellConvFull` of the chains'
readbacks, and chainability transports across the step.  The assembly:

  * `sumEqZero_impliesComponentsZero` — the zero-axiom `Nat` sum split (`Nat.noConfusion`,
    never `Nat.succ_ne_zero`);
  * `hcompOrder_twoCellConv` — the two Godement whiskering orders of a horizontal composite
    are convertible: `(α' ▷) ⊟ (◁ β) ~ (◁ β) ⊟ (α' ▷)`, derived from ONE `interchange`
    instance at identity outer cells plus unit/whisker-identity cleanups;
  * ★ `transposedBlocksChains_readback_convFull` — the SWAP CORE at an ARBITRARY anchor:
    chains over the two transposed middle-block lists have convertible readbacks.  The anchor
    dichotomy (`spineDiffChain_anchored_or_generatorFree`) splits: anchored ⟹ split both
    chains (`split_readback_convFull`), identify the splits (`subsingletonEq`), and convert
    the whiskered blocks (`hcompOrder_twoCellConv`); generator-free ⟹ both lists collapse to
    the tail (`spineDiff_eq_ofGeneratorCountZero` + `castAtoms`) and the readbacks are EQUAL;
  * ★ `SpineGodementStep.readback_convFull` — THE GODEMENT CHAIN LIFT: peel the shared
    leading block (`spineDiff_readback_congruence`), the swap core is the rest;
  * ★ `SpineGodementStep.preservesChainability` — chainability transports across the step
    (`Nonempty`-level: the step is a `Prop`, so the reduct chain cannot be data; anchored ⟹
    split-and-rebuild through the builder, generator-free ⟹ both lists are the shared rest).

Stated over `TwoCellConvFull` per the FREE-2 finding (bare `TwoCellConv` cannot strip the
atom-frame identity whiskers).  Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated
in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The Nat sum split -/

/-- A zero sum has zero components (`Nat.noConfusion` on the successor arm — never
`Nat.succ_ne_zero`, which leaks `propext` in this toolchain). -/
theorem sumEqZero_impliesComponentsZero :
    (leftCount rightCount : Nat) → leftCount + rightCount = 0 →
    leftCount = 0 ∧ rightCount = 0
  | leftCount, 0, sumEq => ⟨by rw [Nat.add_zero] at sumEq; exact sumEq, rfl⟩
  | _, _ + 1, sumEq => by rw [Nat.add_succ] at sumEq; exact Nat.noConfusion sumEq

/-! ## The two Godement whiskering orders convert -/

/-- **The two Godement whiskering orders of a horizontal composite are convertible**:
`(α' ▷ gLow) ⊟ (fHigh ◁ β)  ~  (fMid ◁ β) ⊟ (α' ▷ gMid)`.  Derived from ONE `interchange`
instance at identity outer cells (`interchange (id fMid) α' β (id gMid)`), with the identity
factors dissolved by `vcompIdLeft`/`vcompIdRight` and the whiskered identities by
`whiskerLeftId`/`whiskerRightId` under the step congruences. -/
theorem hcompOrder_twoCellConv {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCellFMid oneCellFHigh : ModalityPath signature.graph sourceMode middleMode}
    {oneCellGLow oneCellGMid : ModalityPath signature.graph middleMode targetMode}
    (cellAlphaUpper : RawTwoCellExpr signature oneCellFMid oneCellFHigh)
    (cellBeta : RawTwoCellExpr signature oneCellGLow oneCellGMid) :
    TwoCellConv signature
      (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerRight oneCellGLow cellAlphaUpper)
        (RawTwoCellExpr.whiskerLeft oneCellFHigh cellBeta))
      (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerLeft oneCellFMid cellBeta)
        (RawTwoCellExpr.whiskerRight oneCellGMid cellAlphaUpper)) := by
  have padTowardRedex : TwoCellConv signature
      (RawTwoCellExpr.hcomp
        (RawTwoCellExpr.vcomp (RawTwoCellExpr.id oneCellFMid) cellAlphaUpper)
        (RawTwoCellExpr.vcomp cellBeta (RawTwoCellExpr.id oneCellGMid)))
      (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerRight oneCellGLow cellAlphaUpper)
        (RawTwoCellExpr.whiskerLeft oneCellFHigh cellBeta)) :=
    TwoCellConv.trans
      (TwoCellConv.ofStep (TwoCellStep.vcompCongrLeft
        (RawTwoCellExpr.whiskerLeft oneCellFHigh
          (RawTwoCellExpr.vcomp cellBeta (RawTwoCellExpr.id oneCellGMid)))
        (TwoCellStep.whiskerRightCongr oneCellGLow
          (TwoCellStep.vcompIdLeft cellAlphaUpper))))
      (TwoCellConv.ofStep (TwoCellStep.vcompCongrRight
        (RawTwoCellExpr.whiskerRight oneCellGLow cellAlphaUpper)
        (TwoCellStep.whiskerLeftCongr oneCellFHigh
          (TwoCellStep.vcompIdRight cellBeta))))
  have interchangeLeg : TwoCellConv signature
      (RawTwoCellExpr.hcomp
        (RawTwoCellExpr.vcomp (RawTwoCellExpr.id oneCellFMid) cellAlphaUpper)
        (RawTwoCellExpr.vcomp cellBeta (RawTwoCellExpr.id oneCellGMid)))
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.hcomp (RawTwoCellExpr.id oneCellFMid) cellBeta)
        (RawTwoCellExpr.hcomp cellAlphaUpper (RawTwoCellExpr.id oneCellGMid))) :=
    TwoCellConv.ofStep (TwoCellStep.interchange (RawTwoCellExpr.id oneCellFMid)
      cellAlphaUpper cellBeta (RawTwoCellExpr.id oneCellGMid))
  have cleanReduct : TwoCellConv signature
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.hcomp (RawTwoCellExpr.id oneCellFMid) cellBeta)
        (RawTwoCellExpr.hcomp cellAlphaUpper (RawTwoCellExpr.id oneCellGMid)))
      (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerLeft oneCellFMid cellBeta)
        (RawTwoCellExpr.whiskerRight oneCellGMid cellAlphaUpper)) :=
    TwoCellConv.trans
      (TwoCellConv.ofStep (TwoCellStep.vcompCongrLeft
        (RawTwoCellExpr.hcomp cellAlphaUpper (RawTwoCellExpr.id oneCellGMid))
        (TwoCellStep.vcompCongrLeft (RawTwoCellExpr.whiskerLeft oneCellFMid cellBeta)
          (TwoCellStep.whiskerRightId oneCellFMid oneCellGLow))))
      (TwoCellConv.trans
        (TwoCellConv.ofStep (TwoCellStep.vcompCongrLeft
          (RawTwoCellExpr.hcomp cellAlphaUpper (RawTwoCellExpr.id oneCellGMid))
          (TwoCellStep.vcompIdLeft (RawTwoCellExpr.whiskerLeft oneCellFMid cellBeta))))
        (TwoCellConv.trans
          (TwoCellConv.ofStep (TwoCellStep.vcompCongrRight
            (RawTwoCellExpr.whiskerLeft oneCellFMid cellBeta)
            (TwoCellStep.vcompCongrRight
              (RawTwoCellExpr.whiskerRight oneCellGMid cellAlphaUpper)
              (TwoCellStep.whiskerLeftId oneCellFHigh oneCellGMid))))
          (TwoCellConv.ofStep (TwoCellStep.vcompCongrRight
            (RawTwoCellExpr.whiskerLeft oneCellFMid cellBeta)
            (TwoCellStep.vcompIdRight
              (RawTwoCellExpr.whiskerRight oneCellGMid cellAlphaUpper))))))
  exact padTowardRedex.symm.trans (interchangeLeg.trans cleanReduct)

/-! ## The swap core at an arbitrary anchor -/

/-- ★ **The swap core**: chains over the two TRANSPOSED middle-block lists — the moving block
`cellAlphaUpper` before `cellBeta` at the low contexts versus after it at the high contexts —
have convertible readbacks at an ARBITRARY anchor.  Anchored case: split both chains at the
pinned frame, identify the splits by chain uniqueness, and convert the whiskered blocks by
`hcompOrder_twoCellConv`.  Generator-free case: both lists collapse onto the shared tail and
the readbacks are equal outright. -/
theorem transposedBlocksChains_readback_convFull {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCellFMid oneCellFHigh : ModalityPath signature.graph sourceMode middleMode}
    {oneCellGLow oneCellGMid : ModalityPath signature.graph middleMode targetMode}
    (cellAlphaUpper : RawTwoCellExpr signature oneCellFMid oneCellFHigh)
    (cellBeta : RawTwoCellExpr signature oneCellGLow oneCellGMid)
    (leftAccumulator : ModalityPath signature.graph overallSource sourceMode)
    (rightAccumulator : ModalityPath signature.graph targetMode overallTarget)
    {anchorPath restTarget : ModalityPath signature.graph overallSource overallTarget}
    {tailAtoms : List (SpineAtom signature overallSource overallTarget)}
    (chainOne : FramedSpineChain signature anchorPath restTarget
      (cellAlphaUpper.spineDiff leftAccumulator (composePath oneCellGLow rightAccumulator)
        (cellBeta.spineDiff (composePath leftAccumulator oneCellFHigh) rightAccumulator
          tailAtoms)))
    (chainTwo : FramedSpineChain signature anchorPath restTarget
      (cellBeta.spineDiff (composePath leftAccumulator oneCellFMid) rightAccumulator
        (cellAlphaUpper.spineDiff leftAccumulator (composePath oneCellGMid rightAccumulator)
          tailAtoms))) :
    TwoCellConvFull signature chainOne.readback chainTwo.readback := by
  cases (RawTwoCellExpr.hcomp cellAlphaUpper cellBeta).spineDiffChain_anchored_or_generatorFree
      leftAccumulator rightAccumulator chainOne with
  | inl anchored =>
      subst anchored
      have leftLeg := FramedSpineChain.split_readback_convFull leftAccumulator
        rightAccumulator (RawTwoCellExpr.hcomp cellAlphaUpper cellBeta) chainOne
      have rightLeg := FramedSpineChain.split_readback_convFull leftAccumulator
        rightAccumulator
        (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerLeft oneCellFMid cellBeta)
          (RawTwoCellExpr.whiskerRight oneCellGMid cellAlphaUpper)) chainTwo
      have splitsEq := FramedSpineChain.subsingletonEq
        ((RawTwoCellExpr.hcomp cellAlphaUpper cellBeta).spineChainSplit leftAccumulator
          rightAccumulator chainOne)
        ((RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerLeft oneCellFMid cellBeta)
          (RawTwoCellExpr.whiskerRight oneCellGMid cellAlphaUpper)).spineChainSplit
          leftAccumulator rightAccumulator chainTwo)
      have middleConv : TwoCellConvFull signature
          (RawTwoCellExpr.vcomp
            (RawTwoCellExpr.whiskerLeft leftAccumulator
              (RawTwoCellExpr.whiskerRight rightAccumulator
                (RawTwoCellExpr.hcomp cellAlphaUpper cellBeta)))
            ((RawTwoCellExpr.hcomp cellAlphaUpper cellBeta).spineChainSplit leftAccumulator
              rightAccumulator chainOne).readback)
          (RawTwoCellExpr.vcomp
            (RawTwoCellExpr.whiskerLeft leftAccumulator
              (RawTwoCellExpr.whiskerRight rightAccumulator
                (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerLeft oneCellFMid cellBeta)
                  (RawTwoCellExpr.whiskerRight oneCellGMid cellAlphaUpper))))
            ((RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerLeft oneCellFMid cellBeta)
              (RawTwoCellExpr.whiskerRight oneCellGMid cellAlphaUpper)).spineChainSplit
              leftAccumulator rightAccumulator chainTwo).readback) := by
        rw [← splitsEq]
        exact TwoCellConvFull.vcompCongrLeft _
          (TwoCellConvFull.whiskerLeftCongr leftAccumulator
            (TwoCellConvFull.whiskerRightCongr rightAccumulator
              (TwoCellConvFull.ofConv (hcompOrder_twoCellConv cellAlphaUpper cellBeta))))
      exact leftLeg.trans (middleConv.trans rightLeg.symm)
  | inr compositeFree =>
      have sumZero : cellAlphaUpper.generatorCount + cellBeta.generatorCount = 0 :=
        compositeFree
      have componentCounts := sumEqZero_impliesComponentsZero cellAlphaUpper.generatorCount
        cellBeta.generatorCount sumZero
      have listOneEq : cellAlphaUpper.spineDiff leftAccumulator
          (composePath oneCellGLow rightAccumulator)
          (cellBeta.spineDiff (composePath leftAccumulator oneCellFHigh) rightAccumulator
            tailAtoms) = tailAtoms := by
        rw [cellBeta.spineDiff_eq_ofGeneratorCountZero
            (composePath leftAccumulator oneCellFHigh) rightAccumulator
            componentCounts.right tailAtoms]
        exact cellAlphaUpper.spineDiff_eq_ofGeneratorCountZero leftAccumulator
          (composePath oneCellGLow rightAccumulator) componentCounts.left tailAtoms
      have listTwoEq : cellBeta.spineDiff (composePath leftAccumulator oneCellFMid)
          rightAccumulator
          (cellAlphaUpper.spineDiff leftAccumulator
            (composePath oneCellGMid rightAccumulator) tailAtoms) = tailAtoms := by
        rw [cellAlphaUpper.spineDiff_eq_ofGeneratorCountZero leftAccumulator
            (composePath oneCellGMid rightAccumulator) componentCounts.left tailAtoms]
        exact cellBeta.spineDiff_eq_ofGeneratorCountZero
          (composePath leftAccumulator oneCellFMid) rightAccumulator
          componentCounts.right tailAtoms
      have chainsEq := FramedSpineChain.subsingletonEq
        (chainOne.castAtoms listOneEq) (chainTwo.castAtoms listTwoEq)
      have readbackEq : chainOne.readback = chainTwo.readback := by
        rw [← FramedSpineChain.castAtoms_readback listOneEq chainOne,
          ← FramedSpineChain.castAtoms_readback listTwoEq chainTwo, chainsEq]
      rw [readbackEq]
      exact TwoCellConvFull.refl _

/-! ## The Godement chain lift -/

/-- ★ **THE GODEMENT CHAIN LIFT (FREE-3)**: one `SpineGodementStep` between chained atom
lists is one `TwoCellConvFull` of the chains' readbacks.  The shared leading block peels off
by the readback congruence; the transposed middle blocks are the swap core; the shared upper
block and rest ride the congruence's universal-anchor hypothesis inside the core's tail. -/
theorem SpineGodementStep.readback_convFull {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (step : SpineGodementStep signature firstList secondList)
    {sourcePath targetPath : ModalityPath signature.graph overallSource overallTarget}
    (chainOne : FramedSpineChain signature sourcePath targetPath firstList)
    (chainTwo : FramedSpineChain signature sourcePath targetPath secondList) :
    TwoCellConvFull signature chainOne.readback chainTwo.readback := by
  cases step with
  | @godement sourceMode middleMode targetMode oneCellFLow oneCellFMid oneCellFHigh
      oneCellGLow oneCellGMid oneCellGHigh cellAlpha cellAlphaUpper cellBeta cellBetaUpper
      leftAcc rightAcc rest =>
      exact RawTwoCellExpr.spineDiff_readback_congruence leftAcc
        (composePath oneCellGLow rightAcc) cellAlpha
        (fun {anchorPath} innerChainOne innerChainTwo =>
          transposedBlocksChains_readback_convFull cellAlphaUpper cellBeta leftAcc rightAcc
            innerChainOne innerChainTwo)
        chainOne chainTwo

/-- ★ **Chainability transports across the Godement step** (`Nonempty`-level — the step is a
`Prop`, so the reduct chain cannot be produced as data).  Anchored case: split the redex
chain at the four-cell composite's domain frame and rebuild through the builder over the
reduct composite (equal boundaries).  Generator-free case: both lists ARE the shared rest. -/
theorem SpineGodementStep.preservesChainability {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (step : SpineGodementStep signature firstList secondList)
    {sourcePath targetPath : ModalityPath signature.graph overallSource overallTarget}
    (redexChainExists : Nonempty (FramedSpineChain signature sourcePath targetPath firstList)) :
    Nonempty (FramedSpineChain signature sourcePath targetPath secondList) := by
  cases step with
  | @godement sourceMode middleMode targetMode oneCellFLow oneCellFMid oneCellFHigh
      oneCellGLow oneCellGMid oneCellGHigh cellAlpha cellAlphaUpper cellBeta cellBetaUpper
      leftAcc rightAcc rest =>
      obtain ⟨redexChain⟩ := redexChainExists
      cases (RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp cellAlpha cellAlphaUpper)
          (RawTwoCellExpr.vcomp cellBeta cellBetaUpper)).spineDiffChain_anchored_or_generatorFree
          leftAcc rightAcc redexChain with
      | inl anchored =>
          subst anchored
          exact ⟨(RawTwoCellExpr.vcomp
            (RawTwoCellExpr.hcomp cellAlpha cellBeta)
            (RawTwoCellExpr.hcomp cellAlphaUpper cellBetaUpper)).spineChainDiff leftAcc
              rightAcc
              ((RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp cellAlpha cellAlphaUpper)
                (RawTwoCellExpr.vcomp cellBeta cellBetaUpper)).spineChainSplit leftAcc
                rightAcc redexChain)⟩
      | inr compositeFree =>
          have sumZero : (cellAlpha.generatorCount + cellAlphaUpper.generatorCount)
              + (cellBeta.generatorCount + cellBetaUpper.generatorCount) = 0 :=
            compositeFree
          have columnCounts := sumEqZero_impliesComponentsZero
            (cellAlpha.generatorCount + cellAlphaUpper.generatorCount)
            (cellBeta.generatorCount + cellBetaUpper.generatorCount) sumZero
          have leftColumn := sumEqZero_impliesComponentsZero cellAlpha.generatorCount
            cellAlphaUpper.generatorCount columnCounts.left
          have rightColumn := sumEqZero_impliesComponentsZero cellBeta.generatorCount
            cellBetaUpper.generatorCount columnCounts.right
          have redexListEq : cellAlpha.spineDiff leftAcc
              (composePath oneCellGLow rightAcc)
              (cellAlphaUpper.spineDiff leftAcc (composePath oneCellGLow rightAcc)
                (cellBeta.spineDiff (composePath leftAcc oneCellFHigh) rightAcc
                  (cellBetaUpper.spineDiff (composePath leftAcc oneCellFHigh) rightAcc rest)))
              = rest := by
            rw [cellBetaUpper.spineDiff_eq_ofGeneratorCountZero
                (composePath leftAcc oneCellFHigh) rightAcc rightColumn.right rest,
              cellBeta.spineDiff_eq_ofGeneratorCountZero (composePath leftAcc oneCellFHigh)
                rightAcc rightColumn.left rest,
              cellAlphaUpper.spineDiff_eq_ofGeneratorCountZero leftAcc
                (composePath oneCellGLow rightAcc) leftColumn.right rest]
            exact cellAlpha.spineDiff_eq_ofGeneratorCountZero leftAcc
              (composePath oneCellGLow rightAcc) leftColumn.left rest
          have reductListEq : cellAlpha.spineDiff leftAcc
              (composePath oneCellGLow rightAcc)
              (cellBeta.spineDiff (composePath leftAcc oneCellFMid) rightAcc
                (cellAlphaUpper.spineDiff leftAcc (composePath oneCellGMid rightAcc)
                  (cellBetaUpper.spineDiff (composePath leftAcc oneCellFHigh) rightAcc rest)))
              = rest := by
            rw [cellBetaUpper.spineDiff_eq_ofGeneratorCountZero
                (composePath leftAcc oneCellFHigh) rightAcc rightColumn.right rest,
              cellAlphaUpper.spineDiff_eq_ofGeneratorCountZero leftAcc
                (composePath oneCellGMid rightAcc) leftColumn.right rest,
              cellBeta.spineDiff_eq_ofGeneratorCountZero (composePath leftAcc oneCellFMid)
                rightAcc rightColumn.left rest]
            exact cellAlpha.spineDiff_eq_ofGeneratorCountZero leftAcc
              (composePath oneCellGLow rightAcc) leftColumn.left rest
          exact ⟨(redexChain.castAtoms redexListEq).castAtoms reductListEq.symm⟩

/-! ## Honesty marker -/

/-- **Honesty marker — the Godement chain lift is SHIPPED (FREE-3).**  One
`SpineGodementStep` between chained lists is one `TwoCellConvFull` of readbacks
(`SpineGodementStep.readback_convFull`), and chainability transports across the step
(`preservesChainability`).  Together with chain existence + the readback conversion (FREE-2)
this is the per-step engine of the generic trace reconstruction (`SpineTraceEquiv` of spines
⟹ `TwoCellConvFull` of cells), which remains the next arc.  `= true`. -/
def fxMode_hasChainGodementStep : Bool := true

end FX1Poly.Polygraph
