import FX1Poly.Typed.HasTypeDescPiVarInversion
import FX1Poly.Typed.HasTypeDescPiContextConversion

/-! Probe: the universe-preserving bare-variable type-code leaf — the unconditional `childConverts` case (for
    #1122's generic former step) at a bare variable.  A variable typed AS A TYPE CODE (at a universe) under the
    source is typed at the SAME universe code under any pointwise-Conv target: invertVar + the context-conv Conv
    + the var rule under tgt + convBackToUniverseCode (pin the classifier back to the universe code). -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

theorem HasTypeDescPi.variableTypeCodeContextConversion {profile : PolyProfile} {scope : Nat}
    {sourceContext targetContext : TypingContext profile scope}
    {index : Fin scope} {level : LevelExpr} {flag : UniverseFlag}
    (typed : HasTypeDescPi profile sourceContext (variableCell index) (universeCodeCell level flag))
    (contextConv : ∀ idx : Fin scope, Conv (sourceContext.lookup idx) (targetContext.lookup idx)) :
    HasTypeDescPi profile targetContext (variableCell index) (universeCodeCell level flag) :=
  (HasTypeDescPi.ofFormation (HasTypeDesc.var targetContext index)).convBackToUniverseCode
    (Conv.trans typed.invertVar (contextConv index))

end FX1Poly.Typed

#print axioms FX1Poly.Typed.HasTypeDescPi.variableTypeCodeContextConversion
