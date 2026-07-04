import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionPathRigidity
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.Spine
import FX1Poly.Polygraph.Computad.WordProblem

/-! # AdjunctionAtomRigidity — seed spine atoms are determined by their arc read-offs (ARC-2a)

The arc fold reads a spine atom ONLY through three lengths — `leftContext.length`,
`generatorDom.length`, `generatorCod.length` — which is why raw-list head extraction is refuted
(right-context blindness).  This brick closes the blindness on the CHAINED fragment: at the
walking adjunction, an atom's three read-off lengths TOGETHER WITH its domain boundary (the
running 1-cell that `SpineBoundaryChained` pins) determine the atom COMPLETELY.  Path rigidity
(ARC-1) pins every path field; the boundary length equation recovers the right context's length;
generator uniqueness pins the 2-cell.

  * `adjunctionTwoCell_unique` — parallel seed 2-cell generators are equal;
  * ★ `adjunctionSpineAtom_eq_of_readOffs` — equal domain boundaries + equal read-off lengths
    force equal atoms.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- Parallel seed 2-cell generators are equal: `unit` and `counit` sit at DISTINCT parallel
boundaries, so each hom of the seed's 2-cell family is a subsingleton. -/
theorem adjunctionTwoCell_unique
    {sourceMode targetMode : adjunctionGraph.Mode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (firstGenerator secondGenerator : AdjunctionTwoCell sourcePath targetPath) :
    firstGenerator = secondGenerator := by
  cases firstGenerator with
  | unit => cases secondGenerator with | unit => rfl
  | counit => cases secondGenerator with | counit => rfl

/-- Left-cancellation for `Nat` addition, hand-rolled (`Nat.add_left_cancel`'s core proof is
propext-tainted; `Nat.zero_add` / `Nat.succ_add` / `Nat.succ.inj` are clean). -/
private theorem natAddLeftCancel (base : Nat) :
    ∀ {leftValue rightValue : Nat},
      base + leftValue = base + rightValue → leftValue = rightValue := by
  induction base with
  | zero =>
      intro leftValue rightValue sumsEqual
      rw [Nat.zero_add, Nat.zero_add] at sumsEqual
      exact sumsEqual
  | succ basePred inductionHypothesis =>
      intro leftValue rightValue sumsEqual
      rw [Nat.succ_add, Nat.succ_add] at sumsEqual
      exact inductionHypothesis (Nat.succ.inj sumsEqual)

/-- ★ **Seed atom rigidity**: two spine atoms at the walking adjunction with the SAME domain
boundary (the chained running 1-cell) and equal arc read-off lengths are EQUAL.  Path rigidity
pins the left context (source + length), the mid modes (heterogeneous rigidity), the generator
dom/cod (parallel rigidity), the right context (its length falls out of the boundary length
equation by left-cancellation), and generator uniqueness pins the 2-cell.  This is exactly the
information the arc structure + `SpineBoundaryChained` provide — the correction that moves head
extraction onto the faithful chained fragment. -/
theorem adjunctionSpineAtom_eq_of_readOffs
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atomA atomB : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (domBoundariesEqual :
      composePath atomA.leftContext (composePath atomA.generatorDom atomA.rightContext)
        = composePath atomB.leftContext (composePath atomB.generatorDom atomB.rightContext))
    (leftLengthsEqual : atomA.leftContext.length = atomB.leftContext.length)
    (domLengthsEqual : atomA.generatorDom.length = atomB.generatorDom.length)
    (codLengthsEqual : atomA.generatorCod.length = atomB.generatorCod.length) :
    atomA = atomB := by
  obtain ⟨leftMidA, rightMidA, leftContextA, generatorDomA, generatorCodA,
    generatorA, rightContextA⟩ := atomA
  obtain ⟨leftMidB, rightMidB, leftContextB, generatorDomB, generatorCodB,
    generatorB, rightContextB⟩ := atomB
  dsimp only at domBoundariesEqual leftLengthsEqual domLengthsEqual codLengthsEqual
  cases adjunctionPathTargets_eq_of_length_eq leftContextA leftContextB leftLengthsEqual
  cases adjunctionPath_eq_of_length_eq leftContextA leftContextB leftLengthsEqual
  cases adjunctionPathTargets_eq_of_length_eq generatorDomA generatorDomB domLengthsEqual
  cases adjunctionPath_eq_of_length_eq generatorDomA generatorDomB domLengthsEqual
  cases adjunctionPath_eq_of_length_eq generatorCodA generatorCodB codLengthsEqual
  have boundaryLengths := congrArg ModalityPath.length domBoundariesEqual
  rw [ModalityPath.length_composePath, ModalityPath.length_composePath,
      ModalityPath.length_composePath, ModalityPath.length_composePath] at boundaryLengths
  have rightLengthsEqual :=
    natAddLeftCancel _ (natAddLeftCancel _ boundaryLengths)
  cases adjunctionPath_eq_of_length_eq rightContextA rightContextB rightLengthsEqual
  rw [adjunctionTwoCell_unique generatorA generatorB]

/-! ## Honesty marker -/

/-- **Honesty marker — seed atom rigidity is SHIPPED (ARC-2a).**  A walking-adjunction spine
atom is determined by its domain boundary + the three arc read-off lengths
(`adjunctionSpineAtom_eq_of_readOffs`), with parallel seed generators unique
(`adjunctionTwoCell_unique`).  This closes the arc fold's right-context blindness on the
boundary-chained fragment.  NOT yet shipped: the chained head extraction itself (ARC-2b — locate
the head atom's arc position inside the second chained list and bubble it front via the FREE-5
swap kit), the chained matching assembly (ARC-3), and the seed `ArcCellReconstruction` instance
(ARC-4).  `= true`. -/
def fxMode_hasAdjunctionAtomRigidity : Bool := true

end FX1Poly.Polygraph
