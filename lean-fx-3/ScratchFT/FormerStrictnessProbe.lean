import FX1Poly.Typed.UniverseFormationStrictness

/-! SCRATCH: dependent-former level strictness (Π/Σ classifier pinned to Type@(lmax dl cl)). -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

theorem HasType.piTyCodeClassifierConv_probe {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1))
    (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
    (contextWellFormed : WfContext context)
    (domainTyped : HasType profile context domainCode (universeCodeCell domainLevel flag))
    (codomainTyped : HasType profile (context.cons domainCode) codomainCode
      (universeCodeCell codomainLevel flag))
    (typed : HasType profile context (piTyCodeCell domainCode codomainCode) classifier) :
    Conv classifier (universeCodeCell (LevelExpr.lmax domainLevel codomainLevel) flag) :=
  HasType.uniqueness contextWellFormed typed
    (HasType.piFormation context domainCode codomainCode domainLevel codomainLevel flag
      domainTyped codomainTyped)

theorem HasType.sigmaTyCodeClassifierConv_probe {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1))
    (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
    (contextWellFormed : WfContext context)
    (domainTyped : HasType profile context domainCode (universeCodeCell domainLevel flag))
    (codomainTyped : HasType profile (context.cons domainCode) codomainCode
      (universeCodeCell codomainLevel flag))
    (typed : HasType profile context (sigmaTyCodeCell domainCode codomainCode) classifier) :
    Conv classifier (universeCodeCell (LevelExpr.lmax domainLevel codomainLevel) flag) :=
  HasType.uniqueness contextWellFormed typed
    (HasType.sigmaFormation context domainCode codomainCode domainLevel codomainLevel flag
      domainTyped codomainTyped)

end FX1Poly.Typed

#print axioms FX1Poly.Typed.HasType.piTyCodeClassifierConv_probe
#print axioms FX1Poly.Typed.HasType.sigmaTyCodeClassifierConv_probe

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

-- concrete closed rejection: Π(Type@0).Type@0 has level lmax 1 1, NOT typed at Type@0.
theorem closedPi_notTypedAtZero_probe {profile : PolyProfile} (flag : UniverseFlag) :
    ¬ HasType profile (TypingContext.empty : TypingContext profile 0)
        (piTyCodeCell (universeCodeCell LevelExpr.lzero flag)
          (universeCodeCell LevelExpr.lzero flag))
        (universeCodeCell LevelExpr.lzero flag) := by
  intro typed
  have conv := HasType.piTyCodeClassifierConv_probe
    (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag)
    LevelExpr.lzero.lsucc LevelExpr.lzero.lsucc flag
    WfContext.emptyIsWellFormed
    (HasType.universeFormation TypingContext.empty LevelExpr.lzero flag)
    (HasType.universeFormation (TypingContext.empty.cons _) LevelExpr.lzero flag)
    typed
  exact absurd (universeCodeCell_inj_of_conv conv).1 (by decide)

end FX1Poly.Typed

#print axioms FX1Poly.Typed.closedPi_notTypedAtZero_probe
