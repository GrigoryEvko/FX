import FX1Poly.Typed.UniverseCodeShape
import FX1Poly.Core.RawConfluence

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

theorem universeCodeCell_inj_of_conv {scope : Nat}
    {leftLevel rightLevel : LevelExpr} {leftFlag rightFlag : UniverseFlag}
    (conv : Conv (universeCodeCell leftLevel leftFlag : RawTerm scope)
      (universeCodeCell rightLevel rightFlag)) :
    leftLevel = rightLevel ∧ leftFlag = rightFlag := by
  have leftNF : RawTerm.isStepNormalForm (universeCodeCell leftLevel leftFlag : RawTerm scope) := rfl
  have rightNF : RawTerm.isStepNormalForm (universeCodeCell rightLevel rightFlag : RawTerm scope) := rfl
  have codesEqual :
      (universeCodeCell leftLevel leftFlag : RawTerm scope) = universeCodeCell rightLevel rightFlag :=
    (Conv.iff_normalForms_eq_of_confluence (StepStar.refl _) leftNF (StepStar.refl _) rightNF).mp conv
  exact universeCodeCell_inj codesEqual

end FX1Poly.Typed

#print axioms FX1Poly.Typed.universeCodeCell_inj_of_conv
