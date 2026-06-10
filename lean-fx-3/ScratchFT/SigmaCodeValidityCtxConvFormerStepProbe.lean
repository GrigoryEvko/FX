import FX1Poly.Typed.HasTypeDescPiContextConversionPiElimReduction
import FX1Poly.Typed.HasTypeDescPiFormerCongruence
import FX1Poly.Typed.HasTypeDescPiInversion

/-! Probe: the Σ-FORMER recursion step of the residual's structural discharge — the exact twin of the Π-former
    step (#1120). The residual ConvContextPreservesPiValidity's Π-engine recurses on component type-codes, which
    can themselves be Σ-codes, so the Σ-former step is a needed companion: given the universe-code-PRESERVING
    context conversions of the domain + codomain type-codes, rebuild IsTypeDescPi tgt (Σ D C) via
    inversionSigmaCodeComponents (decompose) + convContextCondition_cons (cons-lift) + sigmaFormationViaGenArm
    (re-form). -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

theorem HasTypeDescPi.sigmaCodeValidityContextConversionFormerStep {profile : PolyProfile} {scope : Nat}
    {sourceContext targetContext : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainConverts : ∀ {domainLevel : LevelExpr} {domainFlag : UniverseFlag},
      HasTypeDescPi profile sourceContext domainCode (universeCodeCell domainLevel domainFlag) →
      (∀ index : Fin scope, Conv (sourceContext.lookup index) (targetContext.lookup index)) →
      HasTypeDescPi profile targetContext domainCode (universeCodeCell domainLevel domainFlag))
    (codomainConverts : ∀ {codomainLevel : LevelExpr} {codomainFlag : UniverseFlag},
      HasTypeDescPi profile (sourceContext.cons domainCode) codomainCode
        (universeCodeCell codomainLevel codomainFlag) →
      (∀ index : Fin (scope + 1),
        Conv ((sourceContext.cons domainCode).lookup index)
          ((targetContext.cons domainCode).lookup index)) →
      HasTypeDescPi profile (targetContext.cons domainCode) codomainCode
        (universeCodeCell codomainLevel codomainFlag))
    (sigmaValidity : IsTypeDescPi profile sourceContext (sigmaTyCodeCell domainCode codomainCode))
    (contextConv : ∀ index : Fin scope,
      Conv (sourceContext.lookup index) (targetContext.lookup index)) :
    IsTypeDescPi profile targetContext (sigmaTyCodeCell domainCode codomainCode) := by
  obtain ⟨_sigmaLevel, _sigmaFlag, sigmaTyped⟩ := sigmaValidity
  obtain ⟨domainLevel, codomainLevel, flag, domainTyped, codomainTyped⟩ :=
    HasTypeDescPi.inversionSigmaCodeComponents sigmaTyped
  have domainTyped' := domainConverts domainTyped contextConv
  have codomainTyped' :=
    codomainConverts codomainTyped (convContextCondition_cons domainCode contextConv)
  exact ⟨LevelExpr.lmax domainLevel codomainLevel, flag,
    HasTypeDescPi.sigmaFormationViaGenArm targetContext domainCode codomainCode
      domainLevel codomainLevel flag domainTyped' codomainTyped'⟩

end FX1Poly.Typed

#print axioms FX1Poly.Typed.HasTypeDescPi.sigmaCodeValidityContextConversionFormerStep
