import FX1Poly.Typed.ConsistentStratification
import FX1Poly.Typed.ValidTypingConvArm

/-! SCRATCH: #662 stratified conv-variable arm — ConsistentStratification discharges levelMatch. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

theorem convVariableReclassifierOfStratifiedProbe {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) {context : TypingContext profile scope}
    (consistent : ConsistentStratification contextLevels context)
    {termIndex index : Fin scope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    (subjectTypeIsReclassifier : context.lookup termIndex = variableCell index)
    (reclassifierIsUniverse : context.lookup index = universeCodeCell levelExpr flag) :
    TotalBridgeConclusion profile contextLevels context
      (variableCell termIndex) (variableCell index) := by
  refine TotalBridgeConclusion.convVariableReclassifier contextLevels (contextLevels termIndex)
    (classifier := variableCell index) ?subjectValid ?converts reclassifierIsUniverse
    (consistent termIndex index subjectTypeIsReclassifier)
  case subjectValid =>
    rw [← subjectTypeIsReclassifier]
    exact ValidTyping.var contextLevels context termIndex
  case converts =>
    exact Conv.refl _

end FX1Poly.Typed

#print axioms FX1Poly.Typed.convVariableReclassifierOfStratifiedProbe
