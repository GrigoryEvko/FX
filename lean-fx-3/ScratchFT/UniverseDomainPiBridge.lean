import FX1Poly.Typed.LevelingBridge

/-! Scratch: the universe-domain Π formation IS handled in the ValidTyping (per-level) route, by composing
the two shipped bridge pieces. This concretely demonstrates the strategic pivot: where the FUEL all-levels
route stalls at #672 (impredicative member-extension for Π(Type@e)C), the ValidTyping route forms the
universe-domain Π directly via the LEVEL-POLYMORPHIC universeFormation (the domain Type@e is valid at every
level, validTypingForallAboveLevelUniverseDomain), sidestepping the member-extension entirely. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

/-- **Universe-domain Π formation, bridged (the GO case made concrete).**  A dependent function type
`Π (X : Type@innerLevel). C` whose DOMAIN is a universe code is `ValidTyping`-valid: the domain `Type@innerLevel`
is valid at EVERY positive level (`validTypingForallAboveLevelUniverseDomain`, level-polymorphic
`universeFormation`), so `validTypingBridgePiFormation`'s `∀ aboveLevel` domain premise is discharged
directly — no impredicative member-extension (the #672 fuel-route obstruction) needed.  This is why the
`ValidTyping` per-level route closes the universe-domain Π that the fuel all-levels route stalls on. -/
theorem validTypingBridgePiFormation_universeDomain {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (predLevel : Nat)
    {context : TypingContext profile scope}
    (innerLevel : LevelExpr) {codomainCode : RawTerm (scope + 1)}
    {codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    (codomainTyped : ∀ headLevel : Nat,
      ValidTyping profile (levelCons headLevel contextLevels) (predLevel + 1)
        (context.cons (universeCodeCell innerLevel flag)) codomainCode
        (universeCodeCell codomainLevel flag)) :
    ∃ subjectLevel : Nat,
      ValidTyping profile contextLevels subjectLevel context
        (piTyCodeCell (universeCodeCell innerLevel flag) codomainCode)
        (universeCodeCell formerLevel flag) :=
  validTypingBridgePiFormation (formerLevel := formerLevel) contextLevels predLevel
    (validTypingForallAboveLevelUniverseDomain contextLevels context innerLevel flag)
    codomainTyped

end FX1Poly.Typed

#print axioms FX1Poly.Typed.validTypingBridgePiFormation_universeDomain
