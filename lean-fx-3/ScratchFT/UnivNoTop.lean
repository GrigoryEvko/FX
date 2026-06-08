import FX1Poly.Typed.TypedUniverseTower
import FX1Poly.Typed.HasTypeDescPiUniverseCodeInversion

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

-- 1. SHARP CHARACTERIZATION: a universe code's universe-code classifier is EXACTLY its successor (no conv slack).
theorem universeCodeClassifierIsSuccessor {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subjectLevel classifierLevel : LevelExpr} {subjectFlag classifierFlag : UniverseFlag}
    (typed : HasTypeDescPi profile context
      (universeCodeCell subjectLevel subjectFlag) (universeCodeCell classifierLevel classifierFlag)) :
    classifierLevel = subjectLevel.lsucc ∧ classifierFlag = subjectFlag :=
  universeCodeCell_inj_of_conv (HasTypeDescPi.inversionUniverseCode typed)

-- 2. CLASSIFIER UNIQUENESS at a universe code (concrete #469 instance via inversion).
theorem universeCodeClassifierUnique {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subjectLevel : LevelExpr} {subjectFlag : UniverseFlag} {classifierLeft classifierRight : RawTerm scope}
    (typedLeft : HasTypeDescPi profile context (universeCodeCell subjectLevel subjectFlag) classifierLeft)
    (typedRight : HasTypeDescPi profile context (universeCodeCell subjectLevel subjectFlag) classifierRight) :
    Conv classifierLeft classifierRight :=
  Conv.trans (HasTypeDescPi.inversionUniverseCode typedLeft)
    (Conv.sym (HasTypeDescPi.inversionUniverseCode typedRight))

-- 3. NO TOP UNIVERSE: no closed term classifies the whole tower.
theorem universeHierarchyHasNoTop {profile : PolyProfile} (flag : UniverseFlag) :
    ¬ ∃ topClassifier : RawTerm 0,
      ∀ n : Nat, HasTypeDescPi profile TypingContext.empty (universeLevelTower flag n) topClassifier := by
  intro existsTop
  cases existsTop with
  | intro topClassifier classifiesAll =>
      have convAtZero : Conv topClassifier (universeCodeCell (universeLevelOfNat 0).lsucc flag) :=
        HasTypeDescPi.inversionUniverseCode (classifiesAll 0)
      have convAtOne : Conv topClassifier (universeCodeCell (universeLevelOfNat 1).lsucc flag) :=
        HasTypeDescPi.inversionUniverseCode (classifiesAll 1)
      have levelCollision :
          Conv (universeCodeCell (universeLevelOfNat 0).lsucc flag)
            (universeCodeCell (universeLevelOfNat 1).lsucc flag) :=
        Conv.trans (Conv.sym convAtZero) convAtOne
      have depthCollision : universeLevelOfNat 1 = universeLevelOfNat 2 :=
        (universeCodeCell_inj_of_conv levelCollision).left
      exact absurd (universeLevelOfNat_injective depthCollision) (by decide)

end FX1Poly.Typed

#print axioms FX1Poly.Typed.universeCodeClassifierIsSuccessor
#print axioms FX1Poly.Typed.universeCodeClassifierUnique
#print axioms FX1Poly.Typed.universeHierarchyHasNoTop
