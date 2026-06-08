import FX1Poly.Typed.ValidTypingConvArm

/-! Probe: the conv-variable arm SPECIALIZED to a freshly-bound type variable
    (de Bruijn index ⟨0,_⟩ under a piIntro binder). The leveling equation
    `contextLevels ⟨0,_⟩ = subjectLevel + 1` is discharged BY COMPUTATION
    (levelCons's ⟨0,_⟩ branch = headLevel = predLevel+1, when subjectLevel =
    predLevel) — NO synthesis hypothesis. The base case of the level synthesis:
    a binder pins its variable's level, so the eq is automatic. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

theorem TotalBridgeConclusion.convBoundVariableReclassifier {profile : PolyProfile} {scope : Nat}
    (tailLevels : Fin scope → Nat) (predLevel : Nat)
    {context : TypingContext profile (scope + 1)}
    {subject classifier : RawTerm (scope + 1)}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (isLt : 0 < scope + 1)
    (subjectValid : ValidTyping profile (levelCons (predLevel + 1) tailLevels) predLevel context
      subject classifier)
    (converts : Conv classifier (variableCell ⟨0, isLt⟩))
    (reclassifierIsUniverse : context.lookup ⟨0, isLt⟩ = universeCodeCell levelExpr flag) :
    TotalBridgeConclusion profile (levelCons (predLevel + 1) tailLevels) context
      subject (variableCell ⟨0, isLt⟩) :=
  TotalBridgeConclusion.convVariableReclassifier (levelCons (predLevel + 1) tailLevels) predLevel
    subjectValid converts reclassifierIsUniverse rfl

end FX1Poly.Typed

#print axioms FX1Poly.Typed.TotalBridgeConclusion.convBoundVariableReclassifier
