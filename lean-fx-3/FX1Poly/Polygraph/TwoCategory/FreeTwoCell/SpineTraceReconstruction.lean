import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ChainGodementStep

/-! # SpineTraceReconstruction — trace-equivalent spines reconstruct the conversion (FREE-4)

The readback past the `spine` quotient: `SpineTraceEquiv` of two parallel cells' spines
realizes as a `TwoCellConvFull` between the cells — the reconstruction half of the
trace-monoid characterization of free 2-cell conversion, closing the loop with the shipped
soundness (`twoCellConvFull_spineTraceEquiv`).

  * `natAdd_middleFourExchange` — the count rearrangement the interchange permutes;
  * `RawTwoCellExpr.chainNonempty_ofSpineDiffCountEq` — chainability transports between the
    `spineDiff`s of any two same-boundary cells with EQUAL generator counts (anchored ⟹
    split-and-rebuild through the builder; generator-free ⟹ both lists are the shared rest);
  * `SpineTraceEquiv.chainNonempty_iff` — chainability is invariant along the whole trace
    equivalence (the Godement step is the count-preserving transposition, the cons congruence
    re-anchors through the head frame);
  * ★ `SpineTraceEquiv.readback_convFull` — chains over trace-equivalent lists have
    convertible readbacks: one Godement step is the FREE-3 lift, reflexivity is chain
    uniqueness, transitivity threads a transported middle chain, the cons congruence is the
    shared-head peel;
  * ★ `RawTwoCellExpr.twoCellConvFull_ofSpineTraceEquiv` — THE RECONSTRUCTION: anchor both
    cells through their canonical chains (`cellChain` + `cellChain_readback_convFull`) and
    convert the readbacks;
  * ★★ `twoCellConvFull_iff_spineTraceEquiv` — the CHARACTERIZATION: two parallel free
    2-cells are `TwoCellConvFull`-convertible IFF their spines are trace-equivalent.

Stated at `TwoCellConvFull` — the bare `TwoCellConv` form of the reconstruction is FALSE
(no step strips an identity-path whisker, while the spine absorbs it; the FREE-2 finding).
Flips `fxMode_hasSpineTraceReconstruction`.  Raw Lean 4 + Init; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The count rearrangement -/

/-- Middle-four exchange for `Nat` addition — the generator-count rearrangement the Godement
interchange performs (`Nat.add_assoc`/`Nat.add_left_comm` only; both axiom-clean). -/
theorem natAdd_middleFourExchange (firstCount secondCount thirdCount fourthCount : Nat) :
    (firstCount + secondCount) + (thirdCount + fourthCount)
      = (firstCount + thirdCount) + (secondCount + fourthCount) := by
  rw [Nat.add_assoc, Nat.add_left_comm secondCount thirdCount fourthCount, ← Nat.add_assoc]

/-! ## Count-preserving chainability transport -/

/-- Chainability transports between the `spineDiff`s of any two SAME-BOUNDARY cells with
EQUAL generator counts: anchored ⟹ split the given chain at the shared domain frame and
rebuild through the builder at the other cell (shared codomain frame); generator-free ⟹ both
lists collapse onto the shared rest. -/
theorem RawTwoCellExpr.chainNonempty_ofSpineDiffCountEq {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {localSource localTarget : signature.graph.Mode}
    {localDom localCod : ModalityPath signature.graph localSource localTarget}
    (cellFirst cellSecond : RawTwoCellExpr signature localDom localCod)
    (countEq : cellFirst.generatorCount = cellSecond.generatorCount)
    (leftAccumulator : ModalityPath signature.graph overallSource localSource)
    (rightAccumulator : ModalityPath signature.graph localTarget overallTarget)
    {chainSource restTarget : ModalityPath signature.graph overallSource overallTarget}
    {restAtoms : List (SpineAtom signature overallSource overallTarget)}
    (chainExists : Nonempty (FramedSpineChain signature chainSource restTarget
      (cellFirst.spineDiff leftAccumulator rightAccumulator restAtoms))) :
    Nonempty (FramedSpineChain signature chainSource restTarget
      (cellSecond.spineDiff leftAccumulator rightAccumulator restAtoms)) := by
  obtain ⟨chain⟩ := chainExists
  cases cellFirst.spineDiffChain_anchored_or_generatorFree leftAccumulator rightAccumulator
      chain with
  | inl anchored =>
      subst anchored
      exact ⟨cellSecond.spineChainDiff leftAccumulator rightAccumulator
        (cellFirst.spineChainSplit leftAccumulator rightAccumulator chain)⟩
  | inr firstFree =>
      have secondFree : cellSecond.generatorCount = 0 := countEq.symm.trans firstFree
      exact ⟨(chain.castAtoms (cellFirst.spineDiff_eq_ofGeneratorCountZero leftAccumulator
        rightAccumulator firstFree restAtoms)).castAtoms
        (cellSecond.spineDiff_eq_ofGeneratorCountZero leftAccumulator rightAccumulator
          secondFree restAtoms).symm⟩

/-! ## Chainability is a trace invariant -/

/-- Chainability at a fixed anchored boundary is INVARIANT along the trace equivalence: the
Godement step is a count-preserving transposition (both directions through the middle-four
exchange), and the cons congruence re-anchors the tails through the shared head frame. -/
theorem SpineTraceEquiv.chainNonempty_iff {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (equiv : SpineTraceEquiv signature firstList secondList) :
    ∀ {sourcePath targetPath : ModalityPath signature.graph overallSource overallTarget},
      Nonempty (FramedSpineChain signature sourcePath targetPath firstList)
        ↔ Nonempty (FramedSpineChain signature sourcePath targetPath secondList) := by
  induction equiv with
  | ofStep step =>
      intro sourcePath targetPath
      cases step with
      | @godement stepSourceMode stepMiddleMode stepTargetMode oneCellFLow oneCellFMid
          oneCellFHigh oneCellGLow oneCellGMid oneCellGHigh cellAlpha cellAlphaUpper
          cellBeta cellBetaUpper leftAcc rightAcc rest =>
          constructor
          · exact fun chainExists =>
              RawTwoCellExpr.chainNonempty_ofSpineDiffCountEq
                (RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp cellAlpha cellAlphaUpper)
                  (RawTwoCellExpr.vcomp cellBeta cellBetaUpper))
                (RawTwoCellExpr.vcomp (RawTwoCellExpr.hcomp cellAlpha cellBeta)
                  (RawTwoCellExpr.hcomp cellAlphaUpper cellBetaUpper))
                (natAdd_middleFourExchange cellAlpha.generatorCount
                  cellAlphaUpper.generatorCount cellBeta.generatorCount
                  cellBetaUpper.generatorCount)
                leftAcc rightAcc chainExists
          · exact fun chainExists =>
              RawTwoCellExpr.chainNonempty_ofSpineDiffCountEq
                (RawTwoCellExpr.vcomp (RawTwoCellExpr.hcomp cellAlpha cellBeta)
                  (RawTwoCellExpr.hcomp cellAlphaUpper cellBetaUpper))
                (RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp cellAlpha cellAlphaUpper)
                  (RawTwoCellExpr.vcomp cellBeta cellBetaUpper))
                (natAdd_middleFourExchange cellAlpha.generatorCount
                  cellAlphaUpper.generatorCount cellBeta.generatorCount
                  cellBetaUpper.generatorCount).symm
                leftAcc rightAcc chainExists
  | refl _ => intro _ _; exact Iff.rfl
  | symm _ innerIff => intro _ _; exact innerIff.symm
  | trans _ _ firstIff secondIff => intro _ _; exact firstIff.trans secondIff
  | consCongr atom _ innerIff =>
      intro sourcePath targetPath
      constructor
      · intro chainExists
        obtain ⟨chain⟩ := chainExists
        have sourceEq := FramedSpineChain.headSourceEq chain
        subst sourceEq
        obtain ⟨transportedTail⟩ := innerIff.mp ⟨chain.tailChain⟩
        exact ⟨FramedSpineChain.cons atom transportedTail⟩
      · intro chainExists
        obtain ⟨chain⟩ := chainExists
        have sourceEq := FramedSpineChain.headSourceEq chain
        subst sourceEq
        obtain ⟨transportedTail⟩ := innerIff.mpr ⟨chain.tailChain⟩
        exact ⟨FramedSpineChain.cons atom transportedTail⟩

/-! ## Readbacks convert along the trace equivalence -/

/-- ★ **Chains over trace-equivalent lists have convertible readbacks.**  One Godement step
is the FREE-3 lift; reflexivity is chain uniqueness; transitivity threads a middle chain
transported by `chainNonempty_iff`; the cons congruence peels the shared head atom through
the cons-eta view. -/
theorem SpineTraceEquiv.readback_convFull {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (equiv : SpineTraceEquiv signature firstList secondList) :
    ∀ {sourcePath targetPath : ModalityPath signature.graph overallSource overallTarget}
      (chainOne : FramedSpineChain signature sourcePath targetPath firstList)
      (chainTwo : FramedSpineChain signature sourcePath targetPath secondList),
      TwoCellConvFull signature chainOne.readback chainTwo.readback := by
  induction equiv with
  | ofStep step =>
      intro _ _ chainOne chainTwo
      exact step.readback_convFull chainOne chainTwo
  | refl _ =>
      intro _ _ chainOne chainTwo
      rw [FramedSpineChain.subsingletonEq chainOne chainTwo]
      exact TwoCellConvFull.refl _
  | symm _ innerHypothesis =>
      intro _ _ chainOne chainTwo
      exact (innerHypothesis chainTwo chainOne).symm
  | trans equivFirst _ firstHypothesis secondHypothesis =>
      intro sourcePath targetPath chainOne chainThree
      obtain ⟨chainMiddle⟩ := equivFirst.chainNonempty_iff.mp ⟨chainOne⟩
      exact (firstHypothesis chainOne chainMiddle).trans
        (secondHypothesis chainMiddle chainThree)
  | consCongr atom _ innerHypothesis =>
      intro sourcePath targetPath chainOne chainTwo
      have sourceEq := FramedSpineChain.headSourceEq chainOne
      subst sourceEq
      have etaOne : chainOne = FramedSpineChain.cons atom chainOne.tailChain :=
        eq_of_heq (FramedSpineChain.consEtaHeq chainOne)
      have etaTwo : chainTwo = FramedSpineChain.cons atom chainTwo.tailChain :=
        eq_of_heq (FramedSpineChain.consEtaHeq chainTwo)
      rw [etaOne, etaTwo]
      exact TwoCellConvFull.vcompCongrRight _
        (innerHypothesis chainOne.tailChain chainTwo.tailChain)

/-! ## The reconstruction + the characterization -/

/-- ★ **THE RECONSTRUCTION (FREE-4)**: trace-equivalent spines realize as a
`TwoCellConvFull` between the cells — anchor both cells through their canonical chains and
convert the readbacks. -/
theorem RawTwoCellExpr.twoCellConvFull_ofSpineTraceEquiv {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cellFirst cellSecond : RawTwoCellExpr signature sourcePath targetPath)
    (equiv : SpineTraceEquiv signature cellFirst.spine cellSecond.spine) :
    TwoCellConvFull signature cellFirst cellSecond :=
  (RawTwoCellExpr.cellChain_readback_convFull cellFirst).trans
    ((equiv.readback_convFull cellFirst.cellChain cellSecond.cellChain).trans
      (RawTwoCellExpr.cellChain_readback_convFull cellSecond).symm)

/-- ★★ **The trace-monoid CHARACTERIZATION of free 2-cell conversion**: two parallel free
2-cells are `TwoCellConvFull`-convertible IFF their spines are trace-equivalent.  Soundness
is `twoCellConvFull_spineTraceEquiv`; reconstruction is the theorem above.  Deciding
`TwoCellConvFull` is now exactly the list-level Mazurkiewicz word problem on spines. -/
theorem twoCellConvFull_iff_spineTraceEquiv {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cellFirst cellSecond : RawTwoCellExpr signature sourcePath targetPath) :
    TwoCellConvFull signature cellFirst cellSecond
      ↔ SpineTraceEquiv signature cellFirst.spine cellSecond.spine :=
  ⟨twoCellConvFull_spineTraceEquiv,
    RawTwoCellExpr.twoCellConvFull_ofSpineTraceEquiv cellFirst cellSecond⟩

end FX1Poly.Polygraph
