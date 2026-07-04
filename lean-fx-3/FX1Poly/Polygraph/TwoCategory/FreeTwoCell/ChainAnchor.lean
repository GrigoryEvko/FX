import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ChainReadbackCongruence

/-! # ChainAnchor — a chain over a spineDiff is anchored, or the cell is generator-free

The swap core of the Godement chain lift needs the chain's source at the cell's domain frame
(where the split/rebuild machinery lives), but a chain over `cell.spineDiff` at an ARBITRARY
source is only pinned when the cell actually contributes an atom.  This file ships the exact
dichotomy plus the degenerate-case collapse:

  * `RawTwoCellExpr.boundaryEq_ofGeneratorCountZero` — a generator-free cell has equal domain
    and codomain paths (the identity pasting collapses);
  * `RawTwoCellExpr.spineDiff_eq_ofGeneratorCountZero` — a generator-free cell's `spineDiff`
    is the identity on the rest list;
  * `FramedSpineChain.castAtoms` / `castAtoms_readback` — chain transport along an equality
    of the atom-list index (the readback is untouched — its type never mentions the list);
  * ★ `RawTwoCellExpr.spineDiffChain_anchored_or_generatorFree` — the dichotomy: a chain over
    `cell.spineDiff leftAcc rightAcc rest` has its source AT the cell's domain frame, or the
    cell is generator-free (and by the collapse lemmas the list IS the rest and the boundary
    degenerates).

`Nat.noConfusion` for the impossible-count arms (`Nat.succ_ne_zero` leaks `propext` in this
toolchain).  Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Generator-free collapse -/

/-- A generator-free cell has EQUAL domain and codomain paths: with no `gen` leaf the pasting
is built from identities and whiskerings alone, and each arm propagates the equality. -/
theorem RawTwoCellExpr.boundaryEq_ofGeneratorCountZero {signature : ModeSignature} :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    (cell : RawTwoCellExpr signature sourcePath targetPath) →
    cell.generatorCount = 0 → sourcePath = targetPath
  | _, _, _, _, .gen _, countEq => Nat.noConfusion countEq
  | _, _, _, _, .id _, _ => rfl
  | _, _, _, _, .vcomp cellAlpha cellBeta, countEq => by
      cases betaCountForm : cellBeta.generatorCount with
      | zero =>
          have alphaCountZero : cellAlpha.generatorCount = 0 := by
            have countUnfolded : cellAlpha.generatorCount + cellBeta.generatorCount = 0 :=
              countEq
            rw [betaCountForm, Nat.add_zero] at countUnfolded
            exact countUnfolded
          exact (cellAlpha.boundaryEq_ofGeneratorCountZero alphaCountZero).trans
            (cellBeta.boundaryEq_ofGeneratorCountZero betaCountForm)
      | succ priorCount =>
          have countUnfolded : cellAlpha.generatorCount + cellBeta.generatorCount = 0 :=
            countEq
          rw [betaCountForm, Nat.add_succ] at countUnfolded
          exact Nat.noConfusion countUnfolded
  | _, _, _, _, .whiskerLeft oneCell body, countEq =>
      congrArg (composePath oneCell) (body.boundaryEq_ofGeneratorCountZero countEq)
  | _, _, _, _, .whiskerRight oneCell body, countEq =>
      congrArg (fun bodyBoundary => composePath bodyBoundary oneCell)
        (body.boundaryEq_ofGeneratorCountZero countEq)

/-- A generator-free cell's `spineDiff` is the IDENTITY on the rest list — no atom is ever
consed. -/
theorem RawTwoCellExpr.spineDiff_eq_ofGeneratorCountZero {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {localSource localTarget : signature.graph.Mode} →
    (leftAccumulator : ModalityPath signature.graph overallSource localSource) →
    (rightAccumulator : ModalityPath signature.graph localTarget overallTarget) →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    cell.generatorCount = 0 →
    (restAtoms : List (SpineAtom signature overallSource overallTarget)) →
    cell.spineDiff leftAccumulator rightAccumulator restAtoms = restAtoms
  | _, _, _, _, _, _, .gen _, countEq, _ => Nat.noConfusion countEq
  | _, _, _, _, _, _, .id _, _, _ => rfl
  | _, _, leftAccumulator, rightAccumulator, _, _, .vcomp cellAlpha cellBeta, countEq,
      restAtoms => by
      cases betaCountForm : cellBeta.generatorCount with
      | zero =>
          have alphaCountZero : cellAlpha.generatorCount = 0 := by
            have countUnfolded : cellAlpha.generatorCount + cellBeta.generatorCount = 0 :=
              countEq
            rw [betaCountForm, Nat.add_zero] at countUnfolded
            exact countUnfolded
          show cellAlpha.spineDiff leftAccumulator rightAccumulator
              (cellBeta.spineDiff leftAccumulator rightAccumulator restAtoms) = restAtoms
          rw [cellBeta.spineDiff_eq_ofGeneratorCountZero leftAccumulator rightAccumulator
              betaCountForm restAtoms,
            cellAlpha.spineDiff_eq_ofGeneratorCountZero leftAccumulator rightAccumulator
              alphaCountZero restAtoms]
      | succ priorCount =>
          have countUnfolded : cellAlpha.generatorCount + cellBeta.generatorCount = 0 :=
            countEq
          rw [betaCountForm, Nat.add_succ] at countUnfolded
          exact Nat.noConfusion countUnfolded
  | _, _, leftAccumulator, rightAccumulator, _, _, .whiskerLeft oneCell body, countEq,
      restAtoms =>
      body.spineDiff_eq_ofGeneratorCountZero (composePath leftAccumulator oneCell)
        rightAccumulator countEq restAtoms
  | _, _, leftAccumulator, rightAccumulator, _, _, .whiskerRight oneCell body, countEq,
      restAtoms =>
      body.spineDiff_eq_ofGeneratorCountZero leftAccumulator
        (composePath oneCell rightAccumulator) countEq restAtoms

/-! ## Chain transport along a list equality -/

/-- Transport a chain along an equality of its ATOM-LIST index (explicit-motive `Eq.rec`; the
boundary path indices are untouched). -/
def FramedSpineChain.castAtoms {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph overallSource overallTarget}
    {atoms atoms' : List (SpineAtom signature overallSource overallTarget)}
    (atomsEq : atoms = atoms')
    (chain : FramedSpineChain signature sourcePath targetPath atoms) :
    FramedSpineChain signature sourcePath targetPath atoms' :=
  Eq.rec (motive := fun listIndex _ =>
    FramedSpineChain signature sourcePath targetPath listIndex) chain atomsEq

/-- List transport does not move the readback — the readback's type never mentions the atom
list, so the equation is homogeneous and definitional. -/
theorem FramedSpineChain.castAtoms_readback {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph overallSource overallTarget}
    {atoms atoms' : List (SpineAtom signature overallSource overallTarget)}
    (atomsEq : atoms = atoms')
    (chain : FramedSpineChain signature sourcePath targetPath atoms) :
    (chain.castAtoms atomsEq).readback = chain.readback := by
  cases atomsEq; rfl

/-! ## The anchor dichotomy -/

/-- ★ **The anchor dichotomy**: a chain over `cell.spineDiff leftAcc rightAcc rest` has its
source AT the cell's domain frame, OR the cell is generator-free.  `gen` pins via the head
atom's frame (`headSourceEq`), `id` is generator-free, `vcomp` first tries the left factor and
collapses it when free, the whisker arms re-anchor through the `composePath` associativity
seams. -/
theorem RawTwoCellExpr.spineDiffChain_anchored_or_generatorFree {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {localSource localTarget : signature.graph.Mode} →
    (leftAccumulator : ModalityPath signature.graph overallSource localSource) →
    (rightAccumulator : ModalityPath signature.graph localTarget overallTarget) →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    {chainSource restTarget : ModalityPath signature.graph overallSource overallTarget} →
    {restAtoms : List (SpineAtom signature overallSource overallTarget)} →
    FramedSpineChain signature chainSource restTarget
      (cell.spineDiff leftAccumulator rightAccumulator restAtoms) →
    chainSource = composePath leftAccumulator (composePath localDom rightAccumulator)
      ∨ cell.generatorCount = 0
  | _, _, _, _, _, _, .gen _, _, _, _, chain =>
      Or.inl (FramedSpineChain.headSourceEq chain)
  | _, _, _, _, _, _, .id _, _, _, _, _ => Or.inr rfl
  | _, _, leftAccumulator, rightAccumulator, _, _, .vcomp cellAlpha cellBeta, _, _,
      restAtoms, chain => by
      cases cellAlpha.spineDiffChain_anchored_or_generatorFree leftAccumulator
          rightAccumulator chain with
      | inl anchored => exact Or.inl anchored
      | inr alphaCountZero =>
          dsimp only [RawTwoCellExpr.spineDiff] at chain
          rw [cellAlpha.spineDiff_eq_ofGeneratorCountZero leftAccumulator rightAccumulator
              alphaCountZero
              (cellBeta.spineDiff leftAccumulator rightAccumulator restAtoms)] at chain
          cases cellBeta.spineDiffChain_anchored_or_generatorFree leftAccumulator
              rightAccumulator chain with
          | inl anchoredAtMiddle =>
              refine Or.inl ?anchoredAtDomain
              rw [cellAlpha.boundaryEq_ofGeneratorCountZero alphaCountZero]
              exact anchoredAtMiddle
          | inr betaCountZero =>
              refine Or.inr ?compositeFree
              show cellAlpha.generatorCount + cellBeta.generatorCount = 0
              rw [alphaCountZero, betaCountZero]
  | _, _, leftAccumulator, rightAccumulator, _, _, .whiskerLeft oneCell body, _, _, _,
      chain => by
      cases body.spineDiffChain_anchored_or_generatorFree
          (composePath leftAccumulator oneCell) rightAccumulator chain with
      | inl anchored =>
          exact Or.inl (anchored.trans
            (reassocLeftWhisker leftAccumulator oneCell _ rightAccumulator))
      | inr bodyCountZero => exact Or.inr bodyCountZero
  | _, _, leftAccumulator, rightAccumulator, _, _, .whiskerRight oneCell body, _, _, _,
      chain => by
      cases body.spineDiffChain_anchored_or_generatorFree leftAccumulator
          (composePath oneCell rightAccumulator) chain with
      | inl anchored =>
          exact Or.inl (anchored.trans
            (reassocRightWhisker leftAccumulator _ oneCell rightAccumulator))
      | inr bodyCountZero => exact Or.inr bodyCountZero

/-! ## Honesty marker -/

/-- **Honesty marker — the anchor dichotomy is SHIPPED.**  A chain over a cell's `spineDiff`
is source-anchored at the cell's domain frame or the cell is generator-free
(`spineDiffChain_anchored_or_generatorFree`), and the generator-free case collapses both the
boundary (`boundaryEq_ofGeneratorCountZero`) and the list
(`spineDiff_eq_ofGeneratorCountZero`, transported by `castAtoms`).  This reduces the
arbitrary-anchor swap core of the Godement chain lift to its pinned-anchor case.  `= true`. -/
def fxMode_hasChainAnchorDichotomy : Bool := true

end FX1Poly.Polygraph
