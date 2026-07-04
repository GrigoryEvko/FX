import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ReverseSwapRecognizer

/-! # SwapInversion — swap inversion through the witnesses + swap determinacy (FREE-6b)

The exchange lemma's head-swap case must reconstruct what the recognizers see on the OTHER
side of a known swap.  This file inverts `SpineAtomSwap` through the two witness
structures and derives that a swap's data is DETERMINED by either side:

  * `SpineAtomSwap.forwardInversion` — every swap exhibits its LHS pair carrying the
    forward witness `⟨inertPath, rfl, rfl⟩` (the constructor's own data), with the RHS
    exactly the witness's reconstruction (`firstAfterSwap`/`secondAfterSwap`), both by
    `rfl`;
  * `SpineAtomSwap.reverseInversion` — the mirror: the RHS pair carries the reverse
    witness, with the LHS exactly `movedFront`/`stayedBehind`;
  * `AdjacentSwapWitness.inertPathsCoincide` / `ReverseAdjacentSwapWitness
    .inertPathsCoincide` — a pair admits at most ONE inert zone (left-cancellation of the
    free 1-cell monoid), so at most one witness up to its proof fields;
  * the four reconstruction-agreement corollaries (`firstAfterSwapCoincides`,
    `secondAfterSwapCoincides`, `movedFrontCoincides`, `stayedBehindCoincides`);
  * ★ `SpineAtomSwap.rhsDetermined` / `SpineAtomSwap.lhsDetermined` — swap determinacy:
    the LHS determines the RHS and vice versa.  The exchange lemma uses these to pin the
    recognizers' outputs on a known swap without ever double-`cases`-ing the swap
    inductive (no dependent index drilling).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Witness uniqueness -/

/-- A pair admits at most one FORWARD inert zone: both factorizations share the prefix
`leftContext ∘ generatorCod`, and the free 1-cell monoid is left-cancellative. -/
theorem AdjacentSwapWitness.inertPathsCoincide {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {leftAtom rightAtom : SpineAtom signature overallSource overallTarget}
    (witnessOne witnessTwo : AdjacentSwapWitness leftAtom rightAtom) :
    witnessOne.inertPath = witnessTwo.inertPath :=
  composePathLeftCancel (composePath leftAtom.leftContext leftAtom.generatorCod)
    (witnessOne.leftContextFactors.symm.trans witnessTwo.leftContextFactors)

/-- A pair admits at most one REVERSE inert zone (prefix `leftContext ∘ generatorDom`). -/
theorem ReverseAdjacentSwapWitness.inertPathsCoincide {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {headAtom movingAtom : SpineAtom signature overallSource overallTarget}
    (witnessOne witnessTwo : ReverseAdjacentSwapWitness headAtom movingAtom) :
    witnessOne.inertPath = witnessTwo.inertPath :=
  composePathLeftCancel (composePath movingAtom.leftContext movingAtom.generatorDom)
    (witnessOne.headLeftContextFactors.symm.trans witnessTwo.headLeftContextFactors)

/-- Two forward witnesses for the same pair reconstruct the same first atom. -/
theorem AdjacentSwapWitness.firstAfterSwapCoincides {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {leftAtom rightAtom : SpineAtom signature overallSource overallTarget}
    (witnessOne witnessTwo : AdjacentSwapWitness leftAtom rightAtom) :
    witnessOne.firstAfterSwap = witnessTwo.firstAfterSwap :=
  congrArg (fun inertZone => SpineAtom.mk rightAtom.leftMidMode rightAtom.rightMidMode
      (composePath (composePath leftAtom.leftContext leftAtom.generatorDom) inertZone)
      rightAtom.generatorDom rightAtom.generatorCod rightAtom.generator
      rightAtom.rightContext)
    (AdjacentSwapWitness.inertPathsCoincide witnessOne witnessTwo)

/-- Two forward witnesses for the same pair reconstruct the same second atom. -/
theorem AdjacentSwapWitness.secondAfterSwapCoincides {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {leftAtom rightAtom : SpineAtom signature overallSource overallTarget}
    (witnessOne witnessTwo : AdjacentSwapWitness leftAtom rightAtom) :
    witnessOne.secondAfterSwap = witnessTwo.secondAfterSwap :=
  congrArg (fun inertZone => SpineAtom.mk leftAtom.leftMidMode leftAtom.rightMidMode
      leftAtom.leftContext leftAtom.generatorDom leftAtom.generatorCod leftAtom.generator
      (composePath (composePath inertZone rightAtom.generatorCod)
        rightAtom.rightContext))
    (AdjacentSwapWitness.inertPathsCoincide witnessOne witnessTwo)

/-- Two reverse witnesses for the same pair reconstruct the same moved front. -/
theorem ReverseAdjacentSwapWitness.movedFrontCoincides {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {headAtom movingAtom : SpineAtom signature overallSource overallTarget}
    (witnessOne witnessTwo : ReverseAdjacentSwapWitness headAtom movingAtom) :
    witnessOne.movedFront = witnessTwo.movedFront :=
  congrArg (fun inertZone => SpineAtom.mk movingAtom.leftMidMode movingAtom.rightMidMode
      movingAtom.leftContext movingAtom.generatorDom movingAtom.generatorCod
      movingAtom.generator
      (composePath (composePath inertZone headAtom.generatorDom) headAtom.rightContext))
    (ReverseAdjacentSwapWitness.inertPathsCoincide witnessOne witnessTwo)

/-- Two reverse witnesses for the same pair reconstruct the same stayed-behind atom. -/
theorem ReverseAdjacentSwapWitness.stayedBehindCoincides {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {headAtom movingAtom : SpineAtom signature overallSource overallTarget}
    (witnessOne witnessTwo : ReverseAdjacentSwapWitness headAtom movingAtom) :
    witnessOne.stayedBehind = witnessTwo.stayedBehind :=
  congrArg (fun inertZone => SpineAtom.mk headAtom.leftMidMode headAtom.rightMidMode
      (composePath (composePath movingAtom.leftContext movingAtom.generatorCod) inertZone)
      headAtom.generatorDom headAtom.generatorCod headAtom.generator
      headAtom.rightContext)
    (ReverseAdjacentSwapWitness.inertPathsCoincide witnessOne witnessTwo)

/-! ## The inversions -/

/-- **Forward inversion**: every swap exhibits its LHS pair carrying a forward witness,
with the RHS exactly the witness's reconstruction.  The witness is the constructor's own
data (`⟨inertPath, rfl, rfl⟩`), and both list equations are `rfl` — `firstAfterSwap` /
`secondAfterSwap` were written in exactly the constructor's association. -/
theorem SpineAtomSwap.forwardInversion {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (swapStep : SpineAtomSwap signature firstList secondList) :
    ∃ (leftAtom rightAtom : SpineAtom signature overallSource overallTarget)
      (rest : List (SpineAtom signature overallSource overallTarget))
      (witness : AdjacentSwapWitness leftAtom rightAtom),
      firstList = leftAtom :: rightAtom :: rest
        ∧ secondList = witness.firstAfterSwap :: witness.secondAfterSwap :: rest := by
  cases swapStep with
  | @swap swapSourceMode swapMiddleLeft swapMiddleRight swapTargetMode oneCellFMid
      oneCellFHigh oneCellGLow oneCellGMid generatorLeft generatorRight leftAcc inertPath
      rightAcc rest =>
      exact ⟨⟨swapSourceMode, swapMiddleLeft, leftAcc, oneCellFMid, oneCellFHigh,
          generatorLeft, composePath (composePath inertPath oneCellGLow) rightAcc⟩,
        ⟨swapMiddleRight, swapTargetMode,
          composePath (composePath leftAcc oneCellFHigh) inertPath, oneCellGLow,
          oneCellGMid, generatorRight, rightAcc⟩,
        rest, ⟨inertPath, rfl, rfl⟩, rfl, rfl⟩

/-- **Reverse inversion**: every swap exhibits its RHS pair carrying a reverse witness,
with the LHS exactly `movedFront`/`stayedBehind` — the mirror of `forwardInversion`. -/
theorem SpineAtomSwap.reverseInversion {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (swapStep : SpineAtomSwap signature firstList secondList) :
    ∃ (headAtom movingAtom : SpineAtom signature overallSource overallTarget)
      (rest : List (SpineAtom signature overallSource overallTarget))
      (witness : ReverseAdjacentSwapWitness headAtom movingAtom),
      secondList = headAtom :: movingAtom :: rest
        ∧ firstList = witness.movedFront :: witness.stayedBehind :: rest := by
  cases swapStep with
  | @swap swapSourceMode swapMiddleLeft swapMiddleRight swapTargetMode oneCellFMid
      oneCellFHigh oneCellGLow oneCellGMid generatorLeft generatorRight leftAcc inertPath
      rightAcc rest =>
      exact ⟨⟨swapMiddleRight, swapTargetMode,
          composePath (composePath leftAcc oneCellFMid) inertPath, oneCellGLow,
          oneCellGMid, generatorRight, rightAcc⟩,
        ⟨swapSourceMode, swapMiddleLeft, leftAcc, oneCellFMid, oneCellFHigh,
          generatorLeft, composePath (composePath inertPath oneCellGMid) rightAcc⟩,
        rest, ⟨inertPath, rfl, rfl⟩, rfl, rfl⟩

/-! ## Determinacy -/

/-- ★ **The LHS determines the RHS**: two swaps out of the same list land in the same
list.  Both forward inversions expose the shared LHS pair; the inert zones coincide by
left-cancellation; the reconstructions agree by congruence. -/
theorem SpineAtomSwap.rhsDetermined {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {sharedLhs rhsOne rhsTwo : List (SpineAtom signature overallSource overallTarget)}
    (swapOne : SpineAtomSwap signature sharedLhs rhsOne)
    (swapTwo : SpineAtomSwap signature sharedLhs rhsTwo) :
    rhsOne = rhsTwo := by
  obtain ⟨leftAtomOne, rightAtomOne, restOne, witnessOne, lhsShapeOne, rhsShapeOne⟩ :=
    swapOne.forwardInversion
  obtain ⟨leftAtomTwo, rightAtomTwo, restTwo, witnessTwo, lhsShapeTwo, rhsShapeTwo⟩ :=
    swapTwo.forwardInversion
  have listsAgree : leftAtomOne :: rightAtomOne :: restOne
      = leftAtomTwo :: rightAtomTwo :: restTwo := lhsShapeOne.symm.trans lhsShapeTwo
  injection listsAgree with leftAtomsAgree tailsAgree
  injection tailsAgree with rightAtomsAgree restsAgree
  subst leftAtomsAgree
  subst rightAtomsAgree
  subst restsAgree
  rw [rhsShapeOne, rhsShapeTwo,
    AdjacentSwapWitness.firstAfterSwapCoincides witnessOne witnessTwo,
    AdjacentSwapWitness.secondAfterSwapCoincides witnessOne witnessTwo]

/-- ★ **The RHS determines the LHS**: two swaps into the same list start from the same
list — the mirror of `rhsDetermined` through the reverse inversion. -/
theorem SpineAtomSwap.lhsDetermined {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {lhsOne lhsTwo sharedRhs : List (SpineAtom signature overallSource overallTarget)}
    (swapOne : SpineAtomSwap signature lhsOne sharedRhs)
    (swapTwo : SpineAtomSwap signature lhsTwo sharedRhs) :
    lhsOne = lhsTwo := by
  obtain ⟨headAtomOne, movingAtomOne, restOne, witnessOne, rhsShapeOne, lhsShapeOne⟩ :=
    swapOne.reverseInversion
  obtain ⟨headAtomTwo, movingAtomTwo, restTwo, witnessTwo, rhsShapeTwo, lhsShapeTwo⟩ :=
    swapTwo.reverseInversion
  have listsAgree : headAtomOne :: movingAtomOne :: restOne
      = headAtomTwo :: movingAtomTwo :: restTwo := rhsShapeOne.symm.trans rhsShapeTwo
  injection listsAgree with headAtomsAgree tailsAgree
  injection tailsAgree with movingAtomsAgree restsAgree
  subst headAtomsAgree
  subst movingAtomsAgree
  subst restsAgree
  rw [lhsShapeOne, lhsShapeTwo,
    ReverseAdjacentSwapWitness.movedFrontCoincides witnessOne witnessTwo,
    ReverseAdjacentSwapWitness.stayedBehindCoincides witnessOne witnessTwo]

end FX1Poly.Polygraph
