import FX1Poly.Typed.HasTypeDescPiContextConversionPiElimReduction
import FX1Poly.Typed.HasTypeDescPiFormerCongruence
import FX1Poly.Typed.HasTypeDescPiClassifierValidity

/-! Probe: the Π-FORMER recursion step of the GrownCtxConv-5 residual
    `ConvContextPreservesPiValidity`.  Given the universe-code-PRESERVING context-conversion of the domain and
    codomain type-codes (the structural IHs), rebuild the Π-code's validity under the target via
    `inversionPiCodeComponentsUnconditional` (decompose) + `convContextCondition_cons` (cons-lift) +
    `piFormationViaGenArm` (re-form).  Sits between the formation fragment (#1099, base) and the var-headed
    neutral leaf (firing 30 / #1119): the inductive ENGINE of the residual's structural discharge. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

theorem HasTypeDescPi.piCodeValidityContextConversionFormerStep {profile : PolyProfile} {scope : Nat}
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
    (piValidity : IsTypeDescPi profile sourceContext (piTyCodeCell domainCode codomainCode))
    (contextConv : ∀ index : Fin scope,
      Conv (sourceContext.lookup index) (targetContext.lookup index)) :
    IsTypeDescPi profile targetContext (piTyCodeCell domainCode codomainCode) := by
  obtain ⟨_piLevel, _piFlag, piTyped⟩ := piValidity
  obtain ⟨domainLevel, codomainLevel, flag, domainTyped, codomainTyped⟩ :=
    HasTypeDescPi.inversionPiCodeComponentsUnconditional piTyped
  have domainTyped' := domainConverts domainTyped contextConv
  have codomainTyped' :=
    codomainConverts codomainTyped (convContextCondition_cons domainCode contextConv)
  exact ⟨LevelExpr.lmax domainLevel codomainLevel, flag,
    HasTypeDescPi.piFormationViaGenArm targetContext domainCode codomainCode
      domainLevel codomainLevel flag domainTyped' codomainTyped'⟩

end FX1Poly.Typed

#print axioms FX1Poly.Typed.HasTypeDescPi.piCodeValidityContextConversionFormerStep
