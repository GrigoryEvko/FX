import FX1Poly.Tier0.InternalSconing
import FX1Poly.Tier0.FxThinScopeRMC

namespace FX1Poly.Tier0

/-- The representable presheaf sections at `topScope`: Hom(scope, topScope) = PLift (scope <= topScope).
Defined with literal Nat parameters so the `<=` never sees the opaque `.Object` projection. -/
def thinScopeSections (topScope scope : Nat) : Type := PLift (scope ≤ topScope)

def thinScopeGlobalSections (topScope : Nat) :
    GlobalSections.{0, 0, 0} thinScopeCategory where
  terminalObject := topScope
  sections := thinScopeSections topScope
  sectionMap := fun inclusion sectionAtTarget =>
    PLift.up (Nat.le_trans inclusion.down sectionAtTarget.down)
  mapsIdentity := fun _ _ => rfl
  mapsComposition := fun _ _ _ => rfl

#print axioms FX1Poly.Tier0.thinScopeGlobalSections

def thinScopeTautologicalSconing (topScope : Nat) (baseScope : Nat) :
    SconingObject thinScopeCategory (thinScopeGlobalSections topScope) :=
  SconingObject.tautological (thinScopeGlobalSections topScope) baseScope

#print axioms FX1Poly.Tier0.thinScopeTautologicalSconing
