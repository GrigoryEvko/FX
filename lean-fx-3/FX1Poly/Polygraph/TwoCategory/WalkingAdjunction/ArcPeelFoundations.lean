import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionAtomRigidity
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineBoundaryChain

/-! # ArcPeelFoundations — the cup/cap peel's ground facts (ARC-2b brick iii-0)

The cup/cap peel reads the head's partner off the arc structure and pins it by rigidity.
This brick ships the peel's three ground facts:

  * **Classification** — every walking-adjunction spine atom is a CUP (`0 ⟹ 2`, the unit) or
    a CAP (`2 ⟹ 0`, the counit); the arc fold's generic-box arm never fires at the seed.
  * **Boundary-path pinning** — two seed atoms whose domain boundary LENGTHS agree have EQUAL
    domain boundary paths: the composites are parallel adjunction paths of equal length, and
    seed rigidity leaves no freedom.  This upgrades the length-only `SpineBoundaryChained`
    discipline to path-chainedness at the seed for free.
  * **Rigidity at equal boundaries** — combining the two: seed atoms firing at the same
    boundary length with equal arc read-off lengths are EQUAL (the ARC-2a rigidity with its
    path premise discharged by pinning).

A scouting note recorded for honesty: the naive EH-bubble counterexample to head extraction
(a cup/cap circle nested inside the head cap's window) is ILL-TYPED at the seed — the unit
creates `left·right` at base-points while the counit consumes `right·left` at tip-points, so
no circle closes; and snake-chains joining the same bottom ports leave extra events on the
strand that the per-port internal counts distinguish.  The peel's disjointness argument
therefore lives entirely on the typed chained fragment, routed through these pins.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- **Seed classification**: every walking-adjunction spine atom is a cup (`0 ⟹ 2`, the
unit) or a cap (`2 ⟹ 0`, the counit).  The arc fold's generic-box arm never fires at the
seed, so cup/cap event reasoning is exhaustive. -/
theorem adjunctionSpineAtom_isCupOrCap
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atom : SpineAtom adjunctionModeSignature overallSource overallTarget) :
    (atom.generatorDom.length = 0 ∧ atom.generatorCod.length = 2)
      ∨ (atom.generatorDom.length = 2 ∧ atom.generatorCod.length = 0) := by
  obtain ⟨leftMid, rightMid, leftContext, generatorDom, generatorCod, generator,
    rightContext⟩ := atom
  dsimp only
  cases generator with
  | unit => exact Or.inl ⟨rfl, rfl⟩
  | counit => exact Or.inr ⟨rfl, rfl⟩

/-- **Boundary-path pinning**: two seed atoms whose domain boundary LENGTHS agree have equal
domain boundary PATHS — the composites are parallel adjunction paths of equal length, and
seed rigidity (`adjunctionPath_eq_of_length_eq`) pins them.  This discharges the path premise
of `adjunctionSpineAtom_eq_of_readOffs` from the length-only chain discipline. -/
theorem adjunctionAtoms_domBoundaryPathsEqual_of_lengthsEqual
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atomA atomB : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (boundaryLengthsEqual : atomA.domBoundaryLength = atomB.domBoundaryLength) :
    composePath atomA.leftContext (composePath atomA.generatorDom atomA.rightContext)
      = composePath atomB.leftContext (composePath atomB.generatorDom atomB.rightContext) := by
  have compositeLengthsEqual :
      (composePath atomA.leftContext
          (composePath atomA.generatorDom atomA.rightContext)).length
        = (composePath atomB.leftContext
            (composePath atomB.generatorDom atomB.rightContext)).length := by
    rw [ModalityPath.length_composePath, ModalityPath.length_composePath,
        ModalityPath.length_composePath, ModalityPath.length_composePath,
        ← Nat.add_assoc, ← Nat.add_assoc]
    exact boundaryLengthsEqual
  exact adjunctionPath_eq_of_length_eq
    (composePath atomA.leftContext (composePath atomA.generatorDom atomA.rightContext))
    (composePath atomB.leftContext (composePath atomB.generatorDom atomB.rightContext))
    compositeLengthsEqual

/-- ★ **Rigidity at equal boundary lengths**: seed atoms firing at the same boundary length
with equal arc read-off lengths are EQUAL — `adjunctionSpineAtom_eq_of_readOffs` with its
domain-boundary path premise discharged by pinning.  This is the peel's endgame pin: once the
partner is bubbled to the front, it fires at the head's boundary with the head's read-offs,
so it IS the head. -/
theorem adjunctionSpineAtom_eq_of_readOffs_at_equalBoundaryLengths
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atomA atomB : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (boundaryLengthsEqual : atomA.domBoundaryLength = atomB.domBoundaryLength)
    (leftLengthsEqual : atomA.leftContext.length = atomB.leftContext.length)
    (domLengthsEqual : atomA.generatorDom.length = atomB.generatorDom.length)
    (codLengthsEqual : atomA.generatorCod.length = atomB.generatorCod.length) :
    atomA = atomB :=
  adjunctionSpineAtom_eq_of_readOffs atomA atomB
    (adjunctionAtoms_domBoundaryPathsEqual_of_lengthsEqual atomA atomB boundaryLengthsEqual)
    leftLengthsEqual domLengthsEqual codLengthsEqual

/-! ## Honesty marker -/

/-- **Honesty marker — the peel's ground facts are SHIPPED (ARC-2b brick iii-0).**
Classification (every seed atom is a cup or a cap), boundary-path pinning (length-chained ⟹
path-chained at the seed), and rigidity at equal boundary lengths (the peel's endgame pin,
ARC-2a with its path premise discharged).  NOT yet shipped: the arc-position reading lemmas
(locating the head's partner in the second list off the cup/cap event stream) and the peel's
bubbling induction itself.  `= true`. -/
def fxMode_hasArcPeelFoundations : Bool := true

end FX1Poly.Polygraph
