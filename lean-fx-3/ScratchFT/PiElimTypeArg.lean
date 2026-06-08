import FX1Poly.Typed.ValidTypingRefinedMotive

/-! Probe: the piElim arm for a TYPE ARGUMENT (impredicative/polymorphic
    application). When the argument is a type (its classifier is a universe code,
    so it is LEVEL-FLEXIBLE), the same-level alignment ValidTyping.piElim demands
    discharges FOR FREE — instantiate the argument's flexibility at the function's
    level. NO alignment hypothesis. The second synthesis mechanism (after the
    binder-pins-level base case): type arguments float to any level. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

theorem TotalBridgeConclusion.piElimTypeArgument {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (predLevel : Nat)
    {context : TypingContext profile scope}
    {functionTerm argument : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel : LevelExpr} {flag : UniverseFlag}
    (functionTyped : ValidTyping profile contextLevels (predLevel + 1) context
      functionTerm (piTyCodeCell (universeCodeCell domainLevel flag) codomainCode))
    (argumentFlexible : IsLevelFlexibleTypeCode profile contextLevels context argument domainLevel flag)
    (resultNotConvUniverse : ∀ (levelExpr : LevelExpr) (flag : UniverseFlag),
      ¬ Conv (RawTerm.subst0 codomainCode argument) (universeCodeCell levelExpr flag)) :
    TotalBridgeConclusion profile contextLevels context
      (appCell functionTerm argument) (RawTerm.subst0 codomainCode argument) :=
  TotalBridgeConclusion.ofTermValidity
    (ValidTyping.piElim contextLevels (predLevel + 1) functionTyped (argumentFlexible predLevel))
    resultNotConvUniverse

end FX1Poly.Typed

#print axioms FX1Poly.Typed.TotalBridgeConclusion.piElimTypeArgument
