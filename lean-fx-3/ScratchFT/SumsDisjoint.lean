import FX1Poly.Typed.ChurchSums
import FX1Poly.Typed.ClosedNonConvertibility
import FX1Poly.Core.ConvCongruence

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

-- distinguishing handlers: handlerToUniverse returns a universe code; handlerToIdentity returns the identity λ.
def handlerToUniverse : RawTerm 0 :=
  lamCell (RawTerm.weaken (universeCodeCell LevelExpr.lzero UniverseFlag.standard))

def handlerToIdentity : RawTerm 0 :=
  lamCell (RawTerm.weaken combinatorI)

-- handlerToUniverse applied to I reduces to the universe code.
theorem handlerToUniverse_app_I :
    StepStar (appCell handlerToUniverse combinatorI)
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard) := by
  have beta : Step (appCell handlerToUniverse combinatorI)
      (RawTerm.subst0 (RawTerm.weaken (universeCodeCell LevelExpr.lzero UniverseFlag.standard)) combinatorI) :=
    Step.beta
  have cancel : RawTerm.subst0 (RawTerm.weaken (universeCodeCell LevelExpr.lzero UniverseFlag.standard)) combinatorI
      = universeCodeCell LevelExpr.lzero UniverseFlag.standard :=
    RawTerm.weaken_subst_singleton (universeCodeCell LevelExpr.lzero UniverseFlag.standard) combinatorI
  rw [cancel] at beta
  exact StepStar.trans beta (StepStar.refl _)

theorem handlerToIdentity_app_I :
    StepStar (appCell handlerToIdentity combinatorI) combinatorI := by
  have beta : Step (appCell handlerToIdentity combinatorI)
      (RawTerm.subst0 (RawTerm.weaken combinatorI) combinatorI) := Step.beta
  have cancel : RawTerm.subst0 (RawTerm.weaken combinatorI) combinatorI = combinatorI :=
    RawTerm.weaken_subst_singleton combinatorI combinatorI
  rw [cancel] at beta
  exact StepStar.trans beta (StepStar.refl _)

-- THE DISJOINTNESS: the two injections are NOT convertible.
theorem leftInjection_not_conv_rightInjection :
    ¬ Conv (leftInjection combinatorI) (rightInjection combinatorI) := by
  intro hConv
  have congApplied :
      Conv (appCell (appCell (leftInjection combinatorI) handlerToUniverse) handlerToIdentity)
           (appCell (appCell (rightInjection combinatorI) handlerToUniverse) handlerToIdentity) :=
    Conv.app_cong (Conv.app_cong hConv (Conv.refl handlerToUniverse)) (Conv.refl handlerToIdentity)
  have leftReduces :
      StepStar (appCell (appCell (leftInjection combinatorI) handlerToUniverse) handlerToIdentity)
        (universeCodeCell LevelExpr.lzero UniverseFlag.standard) :=
    StepStar.trans_compose (caseLeft_selectsLeftHandler handlerToUniverse handlerToIdentity)
      handlerToUniverse_app_I
  have rightReduces :
      StepStar (appCell (appCell (rightInjection combinatorI) handlerToUniverse) handlerToIdentity)
        combinatorI :=
    StepStar.trans_compose (caseRight_selectsRightHandler handlerToUniverse handlerToIdentity)
      handlerToIdentity_app_I
  have convValues : Conv (universeCodeCell LevelExpr.lzero UniverseFlag.standard) combinatorI :=
    Conv.trans (Conv.sym (Conv.fromStepStar leftReduces))
      (Conv.trans congApplied (Conv.fromStepStar rightReduces))
  exact closedUniverseCode_not_conv_identity LevelExpr.lzero UniverseFlag.standard convValues

end FX1Poly.Typed

#print axioms FX1Poly.Typed.leftInjection_not_conv_rightInjection
