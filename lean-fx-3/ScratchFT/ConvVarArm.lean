import FX1Poly.Typed.UniverseCodeConversion
import FX1Poly.Typed.ValidTypingRefinedMotive
import FX1Poly.Typed.LevelingBridge

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

theorem variableCell_not_conv_universeCodeCell {scope : Nat} (index : Fin scope)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    ¬ Conv (variableCell index : RawTerm scope) (universeCodeCell levelExpr flag) := by
  intro conv
  have variableIsNormal : RawTerm.isStepNormalForm (variableCell index : RawTerm scope) := rfl
  have universeIsNormal : RawTerm.isStepNormalForm (universeCodeCell levelExpr flag : RawTerm scope) := rfl
  have codesEqual : (variableCell index : RawTerm scope) = universeCodeCell levelExpr flag :=
    (Conv.iff_normalForms_eq_of_confluence (StepStar.refl _) variableIsNormal
      (StepStar.refl _) universeIsNormal).mp conv
  have headEq := congrArg RawTerm.headGenerator codesEqual
  rw [headGenerator_variableCell, headGenerator_universeCodeCell] at headEq
  exact absurd headEq (by decide)

theorem RevisedBridgeConclusion.convVariableReclassifier {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (subjectLevel : Nat) {context : TypingContext profile scope}
    {subject classifier : RawTerm scope} {index : Fin scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (subjectValid : ValidTyping profile contextLevels subjectLevel context subject classifier)
    (converts : Conv classifier (variableCell index))
    (reclassifierIsUniverse : context.lookup index = universeCodeCell levelExpr flag)
    (levelMatch : contextLevels index = subjectLevel + 1) :
    RevisedBridgeConclusion profile contextLevels context subject (variableCell index) := by
  refine ⟨⟨subjectLevel, validTypingBridgeConvPinnedReclassifier contextLevels subjectLevel
    subjectValid converts reclassifierIsUniverse levelMatch⟩, ?_⟩
  intro outLevel outFlag reclassifierConvUniverse _subjectNotVariable
  exact absurd reclassifierConvUniverse (variableCell_not_conv_universeCodeCell index outLevel outFlag)

end FX1Poly.Typed

#print axioms FX1Poly.Typed.variableCell_not_conv_universeCodeCell
#print axioms FX1Poly.Typed.RevisedBridgeConclusion.convVariableReclassifier
