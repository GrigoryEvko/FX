import FX1Poly.Typed.PiTypeSaturationReassembly

namespace FX1Poly.Typed

open FX1Poly.Foundation FX1Poly.Universe FX1Poly.Core StepStar

-- The universe-former arm of the all-positive type-reducibility dispatch (#672 type-saturation):
-- Type@levelExpr is reducible-as-a-type at every positive fuel, witnessed by the universe candidate
-- + the universeCode step at each level. The third weak-head shape (neutral #717 / Pi #718 / universe).
theorem IsReducibleTypeAtAllPositiveLevels.ofUniverseCode_probe {scope : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsReducibleTypeAtAllPositiveLevels
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil : RawTerm scope) :=
  fun predLevel =>
    ⟨FX1Poly.Core.universeReducibilityPredicate (FX1Poly.Core.ReducibleTypeAt predLevel),
      FX1Poly.Core.ReducibleTypeStep.universeCode levelExpr flag⟩

end FX1Poly.Typed

#print axioms FX1Poly.Typed.IsReducibleTypeAtAllPositiveLevels.ofUniverseCode_probe
