import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwap

/-! # AtomicMove — one generator atom moves past an arbitrary cell block (FREE-5 core)

The heart of the atomic-generation theorem: a single generator atom in the LEFT column moves
past the ENTIRE spine block of an arbitrary cell in the RIGHT column, inside the atomic swap
closure.  Structural recursion on the passive cell:

  * `gen` — exactly ONE `SpineAtomSwap` (the constructor's shapes were designed to match this
    arm definitionally, inert zone included);
  * `id` — the two lists coincide (reflexivity);
  * `vcomp` — pass the first factor, then the second under the first's moved prefix
    (`prependSpineDiff`); the middle boundary is a shared variable, so NO transports;
  * `whiskerLeft` — recurse with the whiskering 1-cell ABSORBED INTO THE INERT ZONE
    (`inertPath ∘ whiskerCell`), then transport along the four `composePath` associativity
    equalities separating the two spellings;
  * `whiskerRight` — recurse with the whiskering 1-cell absorbed into the right accumulator,
    then transport the moving atom's right contexts along the three-step reassociations.

The inert-zone discipline is what makes the first three arms transport-free and localizes
ALL reassociation to the whisker arms.  Raw Lean 4 + Init; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The atom move**: a generator atom at left context `leftAcc`, separated by an INERT
zone from an arbitrary passive cell's spine block, moves past the whole block inside the
atomic swap closure — the moving atom's right context tracks the passive cell's boundary
(`betaDom ↝ betaCod`) and the block's left accumulator tracks the moving generator's
(`oneCellFHigh ↝ oneCellFMid`). -/
theorem AtomicTraceEquiv.moveGeneratorPastCell {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {swapSourceMode swapMiddleLeft : signature.graph.Mode}
    {oneCellFMid oneCellFHigh : ModalityPath signature.graph swapSourceMode swapMiddleLeft}
    (movingGenerator : signature.twoCell oneCellFMid oneCellFHigh)
    (leftAcc : ModalityPath signature.graph overallSource swapSourceMode) :
    {betaSource betaTarget : signature.graph.Mode} →
    (inertPath : ModalityPath signature.graph swapMiddleLeft betaSource) →
    {betaDom betaCod : ModalityPath signature.graph betaSource betaTarget} →
    (cellBeta : RawTwoCellExpr signature betaDom betaCod) →
    (rightAcc : ModalityPath signature.graph betaTarget overallTarget) →
    (tailAtoms : List (SpineAtom signature overallSource overallTarget)) →
    AtomicTraceEquiv signature
      (⟨_, _, leftAcc, _, _, movingGenerator,
          composePath (composePath inertPath betaDom) rightAcc⟩ ::
        cellBeta.spineDiff (composePath (composePath leftAcc oneCellFHigh) inertPath)
          rightAcc tailAtoms)
      (cellBeta.spineDiff (composePath (composePath leftAcc oneCellFMid) inertPath) rightAcc
        (⟨_, _, leftAcc, _, _, movingGenerator,
            composePath (composePath inertPath betaCod) rightAcc⟩ :: tailAtoms))
  | _, _, inertPath, _, _, .gen passiveGenerator, rightAcc, tailAtoms =>
      AtomicTraceEquiv.ofSwap
        (SpineAtomSwap.swap movingGenerator passiveGenerator leftAcc inertPath rightAcc
          tailAtoms)
  | _, _, inertPath, _, _, .id boundaryPath, rightAcc, tailAtoms =>
      AtomicTraceEquiv.refl _
  | _, _, inertPath, _, _, .vcomp cellFirst cellSecond, rightAcc, tailAtoms =>
      AtomicTraceEquiv.trans
        (AtomicTraceEquiv.moveGeneratorPastCell movingGenerator leftAcc inertPath cellFirst
          rightAcc
          (cellSecond.spineDiff (composePath (composePath leftAcc oneCellFHigh) inertPath)
            rightAcc tailAtoms))
        (AtomicTraceEquiv.prependSpineDiff
          (composePath (composePath leftAcc oneCellFMid) inertPath) rightAcc cellFirst
          (AtomicTraceEquiv.moveGeneratorPastCell movingGenerator leftAcc inertPath
            cellSecond rightAcc tailAtoms))
  | _, _, inertPath, _, _,
      @RawTwoCellExpr.whiskerLeft _ _ _ _ whiskerCell bodyDom bodyCod body, rightAcc,
      tailAtoms => by
      have inner := AtomicTraceEquiv.moveGeneratorPastCell movingGenerator leftAcc
        (composePath inertPath whiskerCell) body rightAcc tailAtoms
      rw [composePath_assoc inertPath whiskerCell bodyDom,
        composePath_assoc inertPath whiskerCell bodyCod,
        ← composePath_assoc (composePath leftAcc oneCellFHigh) inertPath whiskerCell,
        ← composePath_assoc (composePath leftAcc oneCellFMid) inertPath whiskerCell] at inner
      exact inner
  | _, _, inertPath, _, _,
      @RawTwoCellExpr.whiskerRight _ _ _ _ bodyDom bodyCod whiskerCell body, rightAcc,
      tailAtoms => by
      have inner := AtomicTraceEquiv.moveGeneratorPastCell movingGenerator leftAcc inertPath
        body (composePath whiskerCell rightAcc) tailAtoms
      have reassocDom : composePath (composePath inertPath bodyDom)
            (composePath whiskerCell rightAcc)
          = composePath (composePath inertPath (composePath bodyDom whiskerCell))
              rightAcc := by
        rw [composePath_assoc inertPath bodyDom (composePath whiskerCell rightAcc),
          ← composePath_assoc bodyDom whiskerCell rightAcc,
          ← composePath_assoc inertPath (composePath bodyDom whiskerCell) rightAcc]
      have reassocCod : composePath (composePath inertPath bodyCod)
            (composePath whiskerCell rightAcc)
          = composePath (composePath inertPath (composePath bodyCod whiskerCell))
              rightAcc := by
        rw [composePath_assoc inertPath bodyCod (composePath whiskerCell rightAcc),
          ← composePath_assoc bodyCod whiskerCell rightAcc,
          ← composePath_assoc inertPath (composePath bodyCod whiskerCell) rightAcc]
      rw [reassocDom, reassocCod] at inner
      exact inner

end FX1Poly.Polygraph
