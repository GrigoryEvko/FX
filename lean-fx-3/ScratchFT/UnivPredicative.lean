import FX1Poly.Typed.TypedUniverseNoTop

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

-- 1. FULL CHARACTERIZATION: universe-code classification IS the successor relation (both directions).
theorem universeClassificationCharacterization {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subjectLevel classifierLevel : LevelExpr} {subjectFlag classifierFlag : UniverseFlag} :
    HasTypeDescPi profile context
        (universeCodeCell subjectLevel subjectFlag) (universeCodeCell classifierLevel classifierFlag)
      ↔ (classifierLevel = subjectLevel.lsucc ∧ classifierFlag = subjectFlag) := by
  constructor
  · intro typed
    exact universeCodeClassifierIsSuccessor typed
  · intro hyp
    cases hyp with
    | intro levelEq flagEq =>
        subst levelEq
        subst flagEq
        exact HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation context subjectLevel classifierFlag)

-- 2. PREDICATIVITY as non-transitivity (concrete): Type@0:Type@1, Type@1:Type@2, but NOT Type@0:Type@2.
theorem universeClassificationNotTransitive {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescPi profile TypingContext.empty (universeLevelTower flag 0) (universeLevelTower flag 1)
      ∧ HasTypeDescPi profile TypingContext.empty (universeLevelTower flag 1) (universeLevelTower flag 2)
      ∧ ¬ HasTypeDescPi profile TypingContext.empty (universeLevelTower flag 0) (universeLevelTower flag 2) := by
  refine ⟨universeLevelTower_hasTypeDescPi flag 0, universeLevelTower_hasTypeDescPi flag 1, ?_⟩
  intro typed
  have depthEq : universeLevelOfNat 2 = universeLevelOfNat 1 :=
    (universeCodeClassifierIsSuccessor typed).left
  exact absurd (universeLevelOfNat_injective depthEq) (by decide)

-- 3. PREDICATIVITY in general: no universe code is typed two levels up (the engine is non-cumulative).
theorem universeNotCumulativeBySkip {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (subjectLevel : LevelExpr) (flag : UniverseFlag) :
    ¬ HasTypeDescPi profile context
        (universeCodeCell subjectLevel flag) (universeCodeCell subjectLevel.lsucc.lsucc flag) := by
  intro typed
  exact LevelExpr.ne_lsucc_self subjectLevel.lsucc (universeCodeClassifierIsSuccessor typed).left.symm

end FX1Poly.Typed

#print axioms FX1Poly.Typed.universeClassificationCharacterization
#print axioms FX1Poly.Typed.universeClassificationNotTransitive
#print axioms FX1Poly.Typed.universeNotCumulativeBySkip
