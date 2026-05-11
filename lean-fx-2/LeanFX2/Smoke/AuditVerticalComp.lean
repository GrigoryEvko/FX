import LeanFX2.Foundation.Polygraph.VerticalComp

namespace LeanFX2.Smoke

open LeanFX2.Foundation.Polygraph

/-- Anchor cell: a 1-cell from atom 0 to atom 1. -/
def anchorArrow : PolyCell 1 0 1 :=
  PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 0

/-- A second 1-cell parallel to anchorArrow. -/
def parallelArrow : PolyCell 1 0 1 :=
  PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 1

/-- A 2-cell from anchorArrow to parallelArrow. -/
def twoCellAtoB : PolyCell 2 0 1 :=
  PolyCell.cell anchorArrow parallelArrow 100

/-- A third 1-cell parallel to anchorArrow / parallelArrow. -/
def thirdArrow : PolyCell 1 0 1 :=
  PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 2

/-- A 2-cell from parallelArrow to thirdArrow. -/
def twoCellBtoC : PolyCell 2 0 1 :=
  PolyCell.cell parallelArrow thirdArrow 200

/-- Identity chain at anchorArrow has length 0. -/
def identityChain_smoke : VerticalChain anchorArrow anchorArrow :=
  VerticalChain.identity anchorArrow

theorem identityChain_length_smoke :
    identityChain_smoke.length = 0 := rfl

/-- Single-step chain: lift twoCellAtoB into a chain. -/
def singleStepChain_smoke : VerticalChain anchorArrow parallelArrow :=
  VerticalChain.cons twoCellAtoB rfl rfl (VerticalChain.identity parallelArrow)

theorem singleStepChain_length_smoke :
    singleStepChain_smoke.length = 1 := rfl

/-- Length-2 chain composing twoCellAtoB and twoCellBtoC. -/
def twoStepChain_smoke : VerticalChain anchorArrow thirdArrow :=
  VerticalChain.composeTwoCells twoCellAtoB twoCellBtoC rfl rfl rfl rfl

theorem twoStepChain_length_smoke :
    twoStepChain_smoke.length = 2 := rfl

/-- Append two single-step chains, verify length adds to 2. -/
def appendedChain_smoke : VerticalChain anchorArrow thirdArrow :=
  singleStepChain_smoke.append
    (VerticalChain.cons twoCellBtoC rfl rfl (VerticalChain.identity thirdArrow))

theorem appendedChain_length_smoke :
    appendedChain_smoke.length = 2 := rfl

end LeanFX2.Smoke

#print axioms LeanFX2.Foundation.Polygraph.VerticalChain
#print axioms LeanFX2.Foundation.Polygraph.VerticalChain.length
#print axioms LeanFX2.Foundation.Polygraph.VerticalChain.length_identity_eq_zero
#print axioms LeanFX2.Foundation.Polygraph.VerticalChain.length_cons_eq_succ_length_tail
#print axioms LeanFX2.Foundation.Polygraph.VerticalChain.append
#print axioms LeanFX2.Foundation.Polygraph.VerticalChain.append_identity_left
#print axioms LeanFX2.Foundation.Polygraph.VerticalChain.append_cons_unfold
#print axioms LeanFX2.Foundation.Polygraph.VerticalChain.append_identity_right
#print axioms LeanFX2.Foundation.Polygraph.VerticalChain.length_append_eq_sum_of_lengths
#print axioms LeanFX2.Foundation.Polygraph.VerticalChain.composeTwoCells
#print axioms LeanFX2.Foundation.Polygraph.VerticalChain.composeTwoCells_length_eq_two
#print axioms LeanFX2.Smoke.identityChain_smoke
#print axioms LeanFX2.Smoke.identityChain_length_smoke
#print axioms LeanFX2.Smoke.singleStepChain_smoke
#print axioms LeanFX2.Smoke.singleStepChain_length_smoke
#print axioms LeanFX2.Smoke.twoStepChain_smoke
#print axioms LeanFX2.Smoke.twoStepChain_length_smoke
#print axioms LeanFX2.Smoke.appendedChain_smoke
#print axioms LeanFX2.Smoke.appendedChain_length_smoke
