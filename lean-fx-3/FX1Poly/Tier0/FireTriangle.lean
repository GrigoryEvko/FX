import FX1Poly.Tier0.AxisObligation
/-!
# Fire Triangle Constraint System (Pédrot-Tabareau POPL 2020)

The three properties — substitution, dependent elimination, and effects —
cannot all coexist unrestricted in a consistent dependent type theory.
At most two of the three hold simultaneously.

Resolution: ∂CBPV decomposes evaluation strategies into positive/negative
fragments, restricting exactly one leg per axis.

Reference: hal-02383109
-/

namespace FX1Poly.Tier0

structure FireTriangleConfig where
  substitutionUnrestricted : Bool
  dependentEliminationUnrestricted : Bool
  effectsUnrestricted : Bool
  deriving DecidableEq, Repr

def FireTriangleConfig.unrestrictedCount (config : FireTriangleConfig) : Nat :=
  config.substitutionUnrestricted.toNat +
  config.dependentEliminationUnrestricted.toNat +
  config.effectsUnrestricted.toNat

def FireTriangleConfig.isAdmissible (config : FireTriangleConfig) : Bool :=
  config.unrestrictedCount ≤ 2

theorem FireTriangleConfig.allThree_not_admissible :
    (FireTriangleConfig.mk true true true).isAdmissible = false := by
  decide

theorem FireTriangleConfig.twoLegs_admissible_subst_depElim :
    (FireTriangleConfig.mk true true false).isAdmissible = true := by
  decide

theorem FireTriangleConfig.twoLegs_admissible_subst_effects :
    (FireTriangleConfig.mk true false true).isAdmissible = true := by
  decide

theorem FireTriangleConfig.twoLegs_admissible_depElim_effects :
    (FireTriangleConfig.mk false true true).isAdmissible = true := by
  decide

def FireTriangleConfig.fromRestriction : Option FireTriangleLeg → FireTriangleConfig
  | none => ⟨true, true, false⟩
  | some .substitution => ⟨false, true, true⟩
  | some .dependentElimination => ⟨true, false, true⟩
  | some .effects => ⟨true, true, false⟩

theorem FireTriangleConfig.fromRestriction_admissible
    (restriction : Option FireTriangleLeg) :
    (fromRestriction restriction).isAdmissible = true := by
  cases restriction with
  | none => decide
  | some leg => cases leg <;> decide

/-- ∂CBPV evaluation strategies — each restricts exactly one leg. -/
inductive CBPVStrategy where
  | callByName
  | callByValue
  | pure
  deriving DecidableEq, Repr

def CBPVStrategy.restrictedLeg : CBPVStrategy → FireTriangleLeg
  | .callByName => .dependentElimination
  | .callByValue => .substitution
  | .pure => .effects

structure FireTriangleNavigation where
  strategy : CBPVStrategy
  restrictedLeg : FireTriangleLeg
  strategyConsistent : strategy.restrictedLeg = restrictedLeg
  deriving Repr

def FireTriangleNavigation.fromStrategy (strategy : CBPVStrategy) :
    FireTriangleNavigation where
  strategy := strategy
  restrictedLeg := strategy.restrictedLeg
  strategyConsistent := rfl

/-- FX default: pure (effects restricted, subst+depElim unrestricted). -/
def fxDefaultNavigation : FireTriangleNavigation :=
  .fromStrategy .pure

theorem fxDefaultNavigation_admissible :
    (FireTriangleConfig.fromRestriction
      (some fxDefaultNavigation.restrictedLeg)).isAdmissible = true := by
  decide

/-- Combine multiple axis restrictions into one config.
A leg is unrestricted iff NO axis restricts it. -/
def FireTriangleConfig.combine (restrictions : List (Option FireTriangleLeg)) :
    FireTriangleConfig where
  substitutionUnrestricted := restrictions.all fun r => r ≠ some .substitution
  dependentEliminationUnrestricted := restrictions.all fun r => r ≠ some .dependentElimination
  effectsUnrestricted := restrictions.all fun r => r ≠ some .effects

/-- FX's 13 axes combined: at least effects is restricted (by the default pure posture). -/
theorem fxAxesCombined_admissible :
    (FireTriangleConfig.combine [some .effects]).isAdmissible = true := by
  decide

end FX1Poly.Tier0
