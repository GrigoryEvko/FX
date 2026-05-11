import LeanFX2.Foundation.Polygraph.HorizontalComp

namespace LeanFX2.Smoke

open LeanFX2.Foundation.Polygraph

/-- Three dim-1 arrows over the path 0 → 1 → 2 → 3. -/
def firstStepArrow : PolyCell 1 0 1 :=
  PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 10

def secondStepArrow : PolyCell 1 1 2 :=
  PolyCell.arrow (PolyCell.atom 1) (PolyCell.atom 2) 20

def thirdStepArrow : PolyCell 1 2 3 :=
  PolyCell.arrow (PolyCell.atom 2) (PolyCell.atom 3) 30

/-- Identity chain at vertex 5 has length 0. -/
def identityHorizontalChain_smoke : HorizontalChain 5 5 :=
  HorizontalChain.identity 5

theorem identityHorizontalChain_length_smoke :
    identityHorizontalChain_smoke.length = 0 := rfl

/-- Single-step horizontal chain: lift firstStepArrow into a chain. -/
def singleStepHorizontalChain_smoke : HorizontalChain 0 1 :=
  HorizontalChain.cons firstStepArrow (HorizontalChain.identity 1)

theorem singleStepHorizontalChain_length_smoke :
    singleStepHorizontalChain_smoke.length = 1 := rfl

/-- Length-2 chain composing firstStepArrow and secondStepArrow. -/
def twoStepHorizontalChain_smoke : HorizontalChain 0 2 :=
  HorizontalChain.composeTwoArrows firstStepArrow secondStepArrow

theorem twoStepHorizontalChain_length_smoke :
    twoStepHorizontalChain_smoke.length = 2 := rfl

/-- Append two chains, verify length adds. -/
def appendedHorizontalChain_smoke : HorizontalChain 0 3 :=
  twoStepHorizontalChain_smoke.append
    (HorizontalChain.cons thirdStepArrow (HorizontalChain.identity 3))

theorem appendedHorizontalChain_length_smoke :
    appendedHorizontalChain_smoke.length = 3 := rfl

end LeanFX2.Smoke

#print axioms LeanFX2.Foundation.Polygraph.HorizontalChain
#print axioms LeanFX2.Foundation.Polygraph.HorizontalChain.length
#print axioms LeanFX2.Foundation.Polygraph.HorizontalChain.length_identity_eq_zero
#print axioms LeanFX2.Foundation.Polygraph.HorizontalChain.length_cons_eq_succ_length_tail
#print axioms LeanFX2.Foundation.Polygraph.HorizontalChain.append
#print axioms LeanFX2.Foundation.Polygraph.HorizontalChain.append_identity_left
#print axioms LeanFX2.Foundation.Polygraph.HorizontalChain.append_cons_unfold
#print axioms LeanFX2.Foundation.Polygraph.HorizontalChain.append_identity_right
#print axioms LeanFX2.Foundation.Polygraph.HorizontalChain.length_append_eq_sum_of_lengths
#print axioms LeanFX2.Foundation.Polygraph.HorizontalChain.composeTwoArrows
#print axioms LeanFX2.Foundation.Polygraph.HorizontalChain.composeTwoArrows_length_eq_two
#print axioms LeanFX2.Smoke.identityHorizontalChain_smoke
#print axioms LeanFX2.Smoke.identityHorizontalChain_length_smoke
#print axioms LeanFX2.Smoke.singleStepHorizontalChain_smoke
#print axioms LeanFX2.Smoke.singleStepHorizontalChain_length_smoke
#print axioms LeanFX2.Smoke.twoStepHorizontalChain_smoke
#print axioms LeanFX2.Smoke.twoStepHorizontalChain_length_smoke
#print axioms LeanFX2.Smoke.appendedHorizontalChain_smoke
#print axioms LeanFX2.Smoke.appendedHorizontalChain_length_smoke
