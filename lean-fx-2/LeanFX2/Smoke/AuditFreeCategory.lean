import LeanFX2.Foundation.Polygraph.FreeCategory

namespace LeanFX2.Smoke

open LeanFX2.Foundation.Polygraph

/-! Concrete witnesses exercising the K11.7 Burroni free-category API. -/

def freeOneArrow01 : PolyCell 1 0 1 :=
  PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 5

def freeOnePath01_smoke : FreeOneCategory.Morphism 0 1 :=
  FreeOneCategory.fromGenerator freeOneArrow01

theorem freeOnePath01_length_eq_one_smoke :
    freeOnePath01_smoke.length = 1 :=
  FreeOneCategory.fromGenerator_length_eq_one freeOneArrow01

def freeOneIdentityPath0_smoke : FreeOneCategory.Morphism 0 0 :=
  FreeOneCategory.identity 0

theorem freeOneCompose_identity_left_smoke :
    FreeOneCategory.compose freeOneIdentityPath0_smoke freeOnePath01_smoke =
    freeOnePath01_smoke :=
  FreeOneCategory.identity_left freeOnePath01_smoke

def freeOneArrow12 : PolyCell 1 1 2 :=
  PolyCell.arrow (PolyCell.atom 1) (PolyCell.atom 2) 6

def freeOneArrow23 : PolyCell 1 2 3 :=
  PolyCell.arrow (PolyCell.atom 2) (PolyCell.atom 3) 7

def freeOnePath12_smoke : FreeOneCategory.Morphism 1 2 :=
  FreeOneCategory.fromGenerator freeOneArrow12

def freeOnePath23_smoke : FreeOneCategory.Morphism 2 3 :=
  FreeOneCategory.fromGenerator freeOneArrow23

theorem freeOneCompose_assoc_smoke :
    FreeOneCategory.compose
      (FreeOneCategory.compose freeOnePath01_smoke freeOnePath12_smoke)
      freeOnePath23_smoke =
    FreeOneCategory.compose freeOnePath01_smoke
      (FreeOneCategory.compose freeOnePath12_smoke freeOnePath23_smoke) :=
  FreeOneCategory.compose_assoc freeOnePath01_smoke freeOnePath12_smoke
    freeOnePath23_smoke

def freeTwoSourceArrow : PolyCell 1 0 1 :=
  PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 0

def freeTwoTargetArrow : PolyCell 1 0 1 :=
  PolyCell.arrow (PolyCell.atom 0) (PolyCell.atom 1) 1

def freeTwoCellWitness : PolyCell 2 0 1 :=
  PolyCell.cell freeTwoSourceArrow freeTwoTargetArrow 100

def freeTwoChain_smoke :
    FreeTwoCategoryAt.Morphism
      (cellSource freeTwoCellWitness) (cellTarget freeTwoCellWitness) :=
  FreeTwoCategoryAt.fromGenerator freeTwoCellWitness

theorem freeTwoChain_length_eq_one_smoke :
    freeTwoChain_smoke.length = 1 :=
  FreeTwoCategoryAt.fromGenerator_length_eq_one freeTwoCellWitness

end LeanFX2.Smoke

#print axioms LeanFX2.Foundation.Polygraph.FreeOneCategory.compose_assoc
#print axioms LeanFX2.Foundation.Polygraph.FreeOneCategory.identity_left
#print axioms LeanFX2.Foundation.Polygraph.FreeOneCategory.identity_right
#print axioms LeanFX2.Foundation.Polygraph.FreeOneCategory.fromGenerator
#print axioms LeanFX2.Foundation.Polygraph.FreeOneCategory.fromGenerator_length_eq_one
#print axioms LeanFX2.Foundation.Polygraph.FreeTwoCategoryAt.compose_assoc
#print axioms LeanFX2.Foundation.Polygraph.FreeTwoCategoryAt.identity_left
#print axioms LeanFX2.Foundation.Polygraph.FreeTwoCategoryAt.identity_right
#print axioms LeanFX2.Foundation.Polygraph.FreeTwoCategoryAt.fromGenerator
#print axioms LeanFX2.Foundation.Polygraph.FreeTwoCategoryAt.fromGenerator_length_eq_one
#print axioms LeanFX2.Smoke.freeOnePath01_length_eq_one_smoke
#print axioms LeanFX2.Smoke.freeOneCompose_identity_left_smoke
#print axioms LeanFX2.Smoke.freeOneCompose_assoc_smoke
#print axioms LeanFX2.Smoke.freeTwoChain_length_eq_one_smoke
