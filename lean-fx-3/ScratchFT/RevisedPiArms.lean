import FX1Poly.Typed.ValidTypingTermArms
import FX1Poly.Typed.ConvCodeInjectivity

/-! Probe: the REVISED-motive piIntro/piElim term arms (twins of the
    old-motive RefinedTotalBridgeConclusion.piIntro/.piElim), via the
    convertibility-guarded RevisedBridgeConclusion.ofTermValidity. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

theorem RevisedBridgeConclusion.piIntro {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (predLevel : Nat)
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
    (domainTyped : ValidTyping profile contextLevels (predLevel + 1 + 1) context
      domainCode (universeCodeCell domainLevel flag))
    (codomainTyped : ValidTyping profile (levelCons (predLevel + 1) contextLevels)
      (predLevel + 1 + 1) (context.cons domainCode) codomainCode (universeCodeCell codomainLevel flag))
    (bodyTyped : ValidTyping profile (levelCons (predLevel + 1) contextLevels)
      (predLevel + 1) (context.cons domainCode) body codomainCode) :
    RevisedBridgeConclusion profile contextLevels context
      (lamCell body) (piTyCodeCell domainCode codomainCode) :=
  RevisedBridgeConclusion.ofTermValidity
    (ValidTyping.piIntro contextLevels predLevel domainTyped codomainTyped bodyTyped)
    (fun _levelExpr _flag convertibility => Conv.piTyCode_not_universeCode convertibility)

theorem RevisedBridgeConclusion.piElim {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (subjectLevel : Nat)
    {context : TypingContext profile scope}
    {functionTerm argument domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (functionTyped : ValidTyping profile contextLevels subjectLevel context
      functionTerm (piTyCodeCell domainCode codomainCode))
    (argumentTyped : ValidTyping profile contextLevels subjectLevel context argument domainCode)
    (resultNotConvUniverse : ∀ (levelExpr : LevelExpr) (flag : UniverseFlag),
      ¬ Conv (RawTerm.subst0 codomainCode argument) (universeCodeCell levelExpr flag)) :
    RevisedBridgeConclusion profile contextLevels context
      (appCell functionTerm argument) (RawTerm.subst0 codomainCode argument) :=
  RevisedBridgeConclusion.ofTermValidity
    (ValidTyping.piElim contextLevels subjectLevel functionTyped argumentTyped)
    resultNotConvUniverse

end FX1Poly.Typed

#print axioms FX1Poly.Typed.RevisedBridgeConclusion.piIntro
#print axioms FX1Poly.Typed.RevisedBridgeConclusion.piElim
