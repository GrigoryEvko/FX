/-!
# Profile Fibration (Axis 8 — current tower ledger)

This file currently records only finite profile-extension towers and a
small morphism flag record.  It does not construct the profile category,
the Grothendieck fibration, Cisinski localization, or an omega-limit tower.

Reference: Cisinski "Higher Categories and Homotopical Algebra" §2-3.
-/

namespace LeanFX2.Foundation.PolyCell.ProfileFibration

/-- How much of Axis 8 has actually been constructed.

The levels are cumulative.  The current FX profile is `towerDepthOnly`;
later stages must move through explicit data, category, fibration,
localization, and omega-tower constructions instead of inheriting those
claims from comments. -/
inductive ProfileFibrationConstructionLevel where
  /-- Only finite tower shape and depth are wired into `PolyProfile`. -/
  | towerDepthOnly
  /-- A proof-relevant profile-morphism record is wired into the profile axis. -/
  | profileMorphismData
  /-- Profiles and profile morphisms form a constructed category. -/
  | profileCategory
  /-- A Grothendieck fibration over the profile category is constructed. -/
  | grothendieckFibration
  /-- Cisinski-style localization data is constructed. -/
  | cisinskiLocalization
  /-- An omega-depth profile tower or equivalent fixpoint is constructed. -/
  | unboundedProfileTower
  deriving DecidableEq, Repr

/-- Whether this Axis 8 level wires profile-morphism data into the axis. -/
def ProfileFibrationConstructionLevel.hasProfileMorphismData :
    ProfileFibrationConstructionLevel → Bool
  | .towerDepthOnly => false
  | .profileMorphismData => true
  | .profileCategory => true
  | .grothendieckFibration => true
  | .cisinskiLocalization => true
  | .unboundedProfileTower => true

/-- Whether this Axis 8 level includes a constructed category of profiles. -/
def ProfileFibrationConstructionLevel.hasProfileCategory :
    ProfileFibrationConstructionLevel → Bool
  | .towerDepthOnly => false
  | .profileMorphismData => false
  | .profileCategory => true
  | .grothendieckFibration => true
  | .cisinskiLocalization => true
  | .unboundedProfileTower => true

/-- Whether this Axis 8 level includes a Grothendieck fibration. -/
def ProfileFibrationConstructionLevel.hasGrothendieckFibration :
    ProfileFibrationConstructionLevel → Bool
  | .towerDepthOnly => false
  | .profileMorphismData => false
  | .profileCategory => false
  | .grothendieckFibration => true
  | .cisinskiLocalization => true
  | .unboundedProfileTower => true

/-- Whether this Axis 8 level includes Cisinski localization data. -/
def ProfileFibrationConstructionLevel.hasCisinskiLocalization :
    ProfileFibrationConstructionLevel → Bool
  | .towerDepthOnly => false
  | .profileMorphismData => false
  | .profileCategory => false
  | .grothendieckFibration => false
  | .cisinskiLocalization => true
  | .unboundedProfileTower => true

/-- Whether this Axis 8 level includes an omega-depth profile tower. -/
def ProfileFibrationConstructionLevel.hasUnboundedProfileTower :
    ProfileFibrationConstructionLevel → Bool
  | .towerDepthOnly => false
  | .profileMorphismData => false
  | .profileCategory => false
  | .grothendieckFibration => false
  | .cisinskiLocalization => false
  | .unboundedProfileTower => true

/-- The current FX Axis 8 construction level.

Only finite tower depth is wired into `PolyProfile` today. -/
def fxProfileFibrationConstructionLevel :
    ProfileFibrationConstructionLevel :=
  .towerDepthOnly

/-- FX Axis 8 currently wires only finite tower depth into the profile. -/
theorem fxProfileFibrationConstructionLevel_eq :
    fxProfileFibrationConstructionLevel =
      ProfileFibrationConstructionLevel.towerDepthOnly := rfl

/-- FX Axis 8 currently has no wired profile-morphism data. -/
theorem fxProfileFibration_hasNoProfileMorphismData :
    fxProfileFibrationConstructionLevel.hasProfileMorphismData = false := rfl

/-- FX Axis 8 currently has no constructed category of profiles. -/
theorem fxProfileFibration_hasNoProfileCategory :
    fxProfileFibrationConstructionLevel.hasProfileCategory = false := rfl

/-- FX Axis 8 currently has no constructed Grothendieck fibration. -/
theorem fxProfileFibration_hasNoGrothendieckFibration :
    fxProfileFibrationConstructionLevel.hasGrothendieckFibration = false := rfl

/-- FX Axis 8 currently has no constructed Cisinski localization data. -/
theorem fxProfileFibration_hasNoCisinskiLocalization :
    fxProfileFibrationConstructionLevel.hasCisinskiLocalization = false := rfl

/-- FX Axis 8 currently has no omega-depth profile tower. -/
theorem fxProfileFibration_hasNoUnboundedProfileTower :
    fxProfileFibrationConstructionLevel.hasUnboundedProfileTower = false := rfl

/-- A profile morphism flag record.  This is not yet a category-theoretic
morphism between `PolyProfile` values; the full version must map all axis
fields compatibly. -/
structure ProfileMorphismData where
  /-- Whether this morphism is conservative (reflects representability). -/
  isConservative : Bool
  /-- Whether this morphism is faithful (injective on cells). -/
  isFaithful : Bool

namespace ProfileMorphismData

/-- Identity flag morphism: preserves both currently tracked properties. -/
def identity : ProfileMorphismData where
  isConservative := true
  isFaithful := true

/-- Compose two profile-morphism flag records by conjunction of obligations.

This is only flag-level bookkeeping.  It is not a category of profiles because
there is still no action on profile fields or cells. -/
def compose
    (firstMorphism secondMorphism : ProfileMorphismData) :
    ProfileMorphismData where
  isConservative :=
    firstMorphism.isConservative && secondMorphism.isConservative
  isFaithful :=
    firstMorphism.isFaithful && secondMorphism.isFaithful

/-- The identity flag morphism is conservative. -/
theorem identity_isConservative :
    identity.isConservative = true := rfl

/-- The identity flag morphism is faithful. -/
theorem identity_isFaithful :
    identity.isFaithful = true := rfl

/-- Composition computes the conservative flag by Boolean conjunction. -/
theorem compose_isConservative
    (firstMorphism secondMorphism : ProfileMorphismData) :
    (compose firstMorphism secondMorphism).isConservative =
      (firstMorphism.isConservative && secondMorphism.isConservative) := rfl

/-- Composition computes the faithful flag by Boolean conjunction. -/
theorem compose_isFaithful
    (firstMorphism secondMorphism : ProfileMorphismData) :
    (compose firstMorphism secondMorphism).isFaithful =
      (firstMorphism.isFaithful && secondMorphism.isFaithful) := rfl

/-- Left identity preserves the conservative flag. -/
theorem compose_identity_left_isConservative
    (morphism : ProfileMorphismData) :
    (compose identity morphism).isConservative =
      morphism.isConservative := by
  dsimp only [compose, identity]
  cases morphism.isConservative <;> rfl

/-- Left identity preserves the faithful flag. -/
theorem compose_identity_left_isFaithful
    (morphism : ProfileMorphismData) :
    (compose identity morphism).isFaithful =
      morphism.isFaithful := by
  dsimp only [compose, identity]
  cases morphism.isFaithful <;> rfl

/-- Right identity preserves the conservative flag. -/
theorem compose_identity_right_isConservative
    (morphism : ProfileMorphismData) :
    (compose morphism identity).isConservative =
      morphism.isConservative := by
  dsimp only [compose, identity]
  cases morphism.isConservative <;> rfl

/-- Right identity preserves the faithful flag. -/
theorem compose_identity_right_isFaithful
    (morphism : ProfileMorphismData) :
    (compose morphism identity).isFaithful =
      morphism.isFaithful := by
  dsimp only [compose, identity]
  cases morphism.isFaithful <;> rfl

/-- Flag-level composition is associative on the conservative field. -/
theorem compose_assoc_isConservative
    (firstMorphism secondMorphism thirdMorphism : ProfileMorphismData) :
    (compose (compose firstMorphism secondMorphism)
        thirdMorphism).isConservative =
      (compose firstMorphism
        (compose secondMorphism thirdMorphism)).isConservative := by
  dsimp only [compose]
  cases firstMorphism.isConservative <;>
    cases secondMorphism.isConservative <;>
    cases thirdMorphism.isConservative <;> rfl

/-- Flag-level composition is associative on the faithful field. -/
theorem compose_assoc_isFaithful
    (firstMorphism secondMorphism thirdMorphism : ProfileMorphismData) :
    (compose (compose firstMorphism secondMorphism)
        thirdMorphism).isFaithful =
      (compose firstMorphism
        (compose secondMorphism thirdMorphism)).isFaithful := by
  dsimp only [compose]
  cases firstMorphism.isFaithful <;>
    cases secondMorphism.isFaithful <;>
    cases thirdMorphism.isFaithful <;> rfl

/-- Left identity law for flag-level profile morphism data. -/
theorem compose_identity_left (morphism : ProfileMorphismData) :
    compose identity morphism = morphism := by
  cases morphism with
  | mk isConservative isFaithful =>
      cases isConservative <;> cases isFaithful <;> rfl

/-- Right identity law for flag-level profile morphism data. -/
theorem compose_identity_right (morphism : ProfileMorphismData) :
    compose morphism identity = morphism := by
  cases morphism with
  | mk isConservative isFaithful =>
      cases isConservative <;> cases isFaithful <;> rfl

/-- Associativity law for flag-level profile morphism data. -/
theorem compose_assoc
    (firstMorphism secondMorphism thirdMorphism : ProfileMorphismData) :
    compose (compose firstMorphism secondMorphism) thirdMorphism =
      compose firstMorphism (compose secondMorphism thirdMorphism) := by
  cases firstMorphism with
  | mk firstConservative firstFaithful =>
      cases secondMorphism with
      | mk secondConservative secondFaithful =>
          cases thirdMorphism with
          | mk thirdConservative thirdFaithful =>
              cases firstConservative <;> cases firstFaithful <;>
                cases secondConservative <;> cases secondFaithful <;>
                cases thirdConservative <;> cases thirdFaithful <;> rfl

end ProfileMorphismData

/-- A finite profile tower generated by repeated extension. -/
inductive ProfileTower where
  | base
  | extend : ProfileTower → ProfileTower

/-- Depth of a profile tower. -/
def ProfileTower.depth : ProfileTower → Nat
  | .base => 0
  | .extend tower => tower.depth + 1

theorem ProfileTower.base_depth : ProfileTower.base.depth = 0 := rfl

/-- Extend a profile tower by a finite number of one-step profile extensions. -/
def ProfileTower.extendBy : Nat → ProfileTower → ProfileTower
  | 0, tower => tower
  | extensionCount + 1, tower =>
      ProfileTower.extend (ProfileTower.extendBy extensionCount tower)

/-- The depth of a one-step extension is the previous depth plus one. -/
theorem ProfileTower.extend_depth (tower : ProfileTower) :
    (ProfileTower.extend tower).depth = tower.depth + 1 := rfl

/-- Extending by zero steps leaves the tower unchanged. -/
theorem ProfileTower.extendBy_zero (tower : ProfileTower) :
    ProfileTower.extendBy 0 tower = tower := rfl

/-- Extending by a successor count is one extension after the previous count. -/
theorem ProfileTower.extendBy_succ
    (extensionCount : Nat) (tower : ProfileTower) :
    ProfileTower.extendBy (extensionCount + 1) tower =
      ProfileTower.extend (ProfileTower.extendBy extensionCount tower) := rfl

/-- Finite tower extension has the expected additive depth. -/
theorem ProfileTower.extendBy_depth
    (extensionCount : Nat) (tower : ProfileTower) :
    (ProfileTower.extendBy extensionCount tower).depth =
      tower.depth + extensionCount := by
  induction extensionCount with
  | zero => rfl
  | succ previousExtensionCount inductionHypothesis =>
      dsimp only [ProfileTower.extendBy, ProfileTower.depth]
      rw [inductionHypothesis]
      rw [Nat.add_assoc]

/-- The canonical tower obtained by extending the base profile finitely often. -/
def ProfileTower.baseExtendedBy (extensionCount : Nat) : ProfileTower :=
  ProfileTower.extendBy extensionCount ProfileTower.base

/-- The canonical finite extension tower has depth exactly its extension count. -/
theorem ProfileTower.baseExtendedBy_depth (extensionCount : Nat) :
    (ProfileTower.baseExtendedBy extensionCount).depth = extensionCount := by
  dsimp only [ProfileTower.baseExtendedBy]
  rw [ProfileTower.extendBy_depth]
  rw [ProfileTower.base_depth, Nat.zero_add]

end LeanFX2.Foundation.PolyCell.ProfileFibration
