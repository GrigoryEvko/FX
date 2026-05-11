import LeanFX2.Foundation.Polygraph.Laws

namespace LeanFX2.Smoke

open LeanFX2.Foundation.Polygraph

/-! Concrete witnesses exercising K11.6 associativity at small chains. -/

def lawsAnchorArrow : PolyCell 1 0 1 :=
  PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 0

def lawsParallelArrow : PolyCell 1 0 1 :=
  PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 1

def lawsThirdArrow : PolyCell 1 0 1 :=
  PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 2

def lawsTwoCellAtoB : PolyCell 2 0 1 :=
  PolyCell.cell lawsAnchorArrow lawsParallelArrow 100

def lawsTwoCellBtoC : PolyCell 2 0 1 :=
  PolyCell.cell lawsParallelArrow lawsThirdArrow 200

def lawsChainAtoB : VerticalChain lawsAnchorArrow lawsParallelArrow :=
  VerticalChain.cons lawsTwoCellAtoB rfl rfl (VerticalChain.identity lawsParallelArrow)

def lawsChainBtoC : VerticalChain lawsParallelArrow lawsThirdArrow :=
  VerticalChain.cons lawsTwoCellBtoC rfl rfl (VerticalChain.identity lawsThirdArrow)

def lawsChainAnchorIdentity : VerticalChain lawsAnchorArrow lawsAnchorArrow :=
  VerticalChain.identity lawsAnchorArrow

theorem vertical_append_assoc_smoke :
    VerticalChain.append
      (VerticalChain.append lawsChainAnchorIdentity lawsChainAtoB) lawsChainBtoC =
    VerticalChain.append
      lawsChainAnchorIdentity (VerticalChain.append lawsChainAtoB lawsChainBtoC) :=
  VerticalChain.append_assoc lawsChainAnchorIdentity lawsChainAtoB lawsChainBtoC

def lawsArrowStep01 : PolyCell 1 0 1 :=
  PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 10

def lawsArrowStep12 : PolyCell 1 1 2 :=
  PolyCell.arrow (PolyCell.atom 1) (PolyCell.atom 2) 20

def lawsArrowStep23 : PolyCell 1 2 3 :=
  PolyCell.arrow (PolyCell.atom 2) (PolyCell.atom 3) 30

def lawsHorizChain01 : HorizontalChain 0 1 :=
  HorizontalChain.cons lawsArrowStep01 (HorizontalChain.identity 1)

def lawsHorizChain12 : HorizontalChain 1 2 :=
  HorizontalChain.cons lawsArrowStep12 (HorizontalChain.identity 2)

def lawsHorizChain23 : HorizontalChain 2 3 :=
  HorizontalChain.cons lawsArrowStep23 (HorizontalChain.identity 3)

theorem horizontal_append_assoc_smoke :
    HorizontalChain.append
      (HorizontalChain.append lawsHorizChain01 lawsHorizChain12) lawsHorizChain23 =
    HorizontalChain.append
      lawsHorizChain01 (HorizontalChain.append lawsHorizChain12 lawsHorizChain23) :=
  HorizontalChain.append_assoc lawsHorizChain01 lawsHorizChain12 lawsHorizChain23

end LeanFX2.Smoke

#print axioms LeanFX2.Foundation.Polygraph.VerticalChain.append_assoc
#print axioms LeanFX2.Foundation.Polygraph.HorizontalChain.append_assoc
#print axioms LeanFX2.Smoke.vertical_append_assoc_smoke
#print axioms LeanFX2.Smoke.horizontal_append_assoc_smoke
