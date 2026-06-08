import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Typed.HasTypeDescSubjectReduction

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

-- ofFormation routing arm: formation subjects admit no step, so SR is vacuous
theorem HasTypeDescPi.subjectReductionAtOfFormation {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier reduct : RawTerm scope}
    (formationTyped : HasTypeDesc profile context subject classifier)
    (step : Step subject reduct) :
    HasTypeDescPi profile context reduct classifier :=
  absurd step (formationTyped.subjectAdmitsNoStep reduct)

-- conv routing arm: re-wrap the (already SR'd) inner reduct at the reclassifier
theorem HasTypeDescPi.subjectReductionAtConv {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {reduct reclassifier classifier : RawTerm scope}
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (innerReductTyped : HasTypeDescPi profile context reduct classifier)
    (converts : Conv classifier reclassifier)
    (reclassifierTyped : HasTypeDescPi profile context reclassifier
      (universeCodeCell levelExpr flag)) :
    HasTypeDescPi profile context reduct reclassifier :=
  HasTypeDescPi.conv levelExpr flag innerReductTyped converts reclassifierTyped

#print axioms HasTypeDescPi.subjectReductionAtOfFormation
#print axioms HasTypeDescPi.subjectReductionAtConv

end FX1Poly.Typed
