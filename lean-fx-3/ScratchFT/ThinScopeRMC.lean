import FX1Poly.Tier0.RepresentableMapCategory

namespace FX1Poly.Tier0

/-- propext-free structural meet (min) on scopes. -/
def meetScopes : Nat → Nat → Nat
  | 0, _ => 0
  | _+1, 0 => 0
  | scopeA+1, scopeB+1 => (meetScopes scopeA scopeB) + 1

theorem meetScopes_le_left : ∀ (scopeA scopeB : Nat), meetScopes scopeA scopeB ≤ scopeA
  | 0, _ => Nat.le.refl
  | _+1, 0 => Nat.zero_le _
  | scopeA+1, scopeB+1 => Nat.succ_le_succ (meetScopes_le_left scopeA scopeB)

theorem meetScopes_le_right : ∀ (scopeA scopeB : Nat), meetScopes scopeA scopeB ≤ scopeB
  | 0, _ => Nat.zero_le _
  | _+1, 0 => Nat.le.refl
  | scopeA+1, scopeB+1 => Nat.succ_le_succ (meetScopes_le_right scopeA scopeB)

theorem le_meetScopes : ∀ (candidate scopeA scopeB : Nat),
    candidate ≤ scopeA → candidate ≤ scopeB → candidate ≤ meetScopes scopeA scopeB
  | 0, _, _, _, _ => Nat.zero_le _
  | _+1, 0, _, inclusionA, _ => absurd inclusionA (Nat.not_succ_le_zero _)
  | _+1, _+1, 0, _, inclusionB => absurd inclusionB (Nat.not_succ_le_zero _)
  | candidate+1, scopeA+1, scopeB+1, inclusionA, inclusionB =>
      Nat.succ_le_succ (le_meetScopes candidate scopeA scopeB
        (Nat.le_of_succ_le_succ inclusionA) (Nat.le_of_succ_le_succ inclusionB))

theorem meetScopes_eq_right_of_le : ∀ (scopeA scopeB : Nat),
    scopeB ≤ scopeA → meetScopes scopeA scopeB = scopeB
  | 0, 0, _ => rfl
  | _+1, 0, _ => rfl
  | 0, _+1, inclusion => absurd inclusion (Nat.not_succ_le_zero _)
  | scopeA+1, scopeB+1, inclusion =>
      congrArg (· + 1) (meetScopes_eq_right_of_le scopeA scopeB (Nat.le_of_succ_le_succ inclusion))

def thinScopeCategory : RawCategory.{0, 0} where
  Object := Nat
  Morphism := fun scopeA scopeB => PLift (scopeA ≤ scopeB)
  identity := fun scope => PLift.up (Nat.le_refl scope)
  compose := fun inclusionAB inclusionBC => PLift.up (Nat.le_trans inclusionAB.down inclusionBC.down)
  composeAssoc := fun _ _ _ => rfl
  identityLeft := fun _ => rfl
  identityRight := fun _ => rfl

def thinScopeRepresentableMaps : MorphismClass thinScopeCategory where
  member := fun {scopeA scopeB} _inclusion => scopeA = scopeB
  memberDecidable := fun {scopeA scopeB} _inclusion => Nat.decEq scopeA scopeB

def thinScopeRMC : RepresentableMapCategory.{0, 0} where
  underlying := thinScopeCategory
  representableMaps := thinScopeRepresentableMaps
  closedUnderPullback := by
    intro scopeA scopeB scopeC inclusionAC inclusionBC memberAC
    have equalityAC : scopeA = scopeC := memberAC
    have inclusionBA := Nat.le_trans inclusionBC.down (Nat.le_of_eq equalityAC.symm)
    refine ⟨{
      pullbackObject := meetScopes scopeA scopeB
      projectionLeft := PLift.up (meetScopes_le_left scopeA scopeB)
      projectionRight := PLift.up (meetScopes_le_right scopeA scopeB)
      commutes := rfl
      isUniversal := by
        intro candidateObject candidateLeft candidateRight _
        exact ⟨PLift.up (le_meetScopes candidateObject scopeA scopeB
          candidateLeft.down candidateRight.down), rfl, rfl⟩
    }, ?_⟩
    exact meetScopes_eq_right_of_le scopeA scopeB inclusionBA
  isomorphismsRepresentable := by
    intro scopeA scopeB inclusion iso
    exact Nat.le_antisymm inclusion.down iso.inverse.down
  closedUnderComposition := by
    intro scopeA scopeB scopeC _ _ memberAB memberBC
    exact memberAB.trans memberBC

#print axioms FX1Poly.Tier0.thinScopeRMC

end FX1Poly.Tier0
