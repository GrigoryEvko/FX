import FX1Poly.Typed.MetatheoryFuzz
import FX1Poly.Typed.GrownCanonicalFormsByClassifier
import FX1Poly.Typed.TypedNormalizer

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

theorem arrowType1Type1 {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescPi profile
      (TypingContext.empty.cons (universeCodeCell LevelExpr.lzero.lsucc flag))
      (piTyCodeCell (universeCodeCell LevelExpr.lzero.lsucc flag)
        (universeCodeCell LevelExpr.lzero.lsucc flag))
      (universeCodeCell (lmaxAll [LevelExpr.lzero.lsucc.lsucc, LevelExpr.lzero.lsucc.lsucc]) flag) := by
  refine HasTypeDescPi.genFormationPi _ .gen_piTyCode () _
    [LevelExpr.lzero.lsucc.lsucc, LevelExpr.lzero.lsucc.lsucc] flag
    { outputType := universeFormerOutput } rfl ?premises
  refine DescTelescopePi.cons _ _ _ _ _ _ ?domainTyped ?codomainTelescope
  · exact HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation _ LevelExpr.lzero.lsucc flag)
  · refine DescTelescopePi.cons _ _ _ _ _ _ ?codomainTyped ?nilTelescope
    · exact HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation _ LevelExpr.lzero.lsucc flag)
    · exact DescTelescopePi.nil _ _

theorem nestedConstantLambdaTyping {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescPi profile TypingContext.empty
      (lamCell (lamCell (universeCodeCell LevelExpr.lzero flag)))
      (piTyCodeCell (universeCodeCell LevelExpr.lzero.lsucc flag)
        (piTyCodeCell (universeCodeCell LevelExpr.lzero.lsucc flag)
          (universeCodeCell LevelExpr.lzero.lsucc flag))) := by
  refine HasTypeDescPi.piIntro LevelExpr.lzero.lsucc.lsucc
    (lmaxAll [LevelExpr.lzero.lsucc.lsucc, LevelExpr.lzero.lsucc.lsucc]) flag
    ?domainTyped ?codomainTyped ?bodyTyped
  · exact HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero.lsucc flag)
  · exact arrowType1Type1 flag
  · refine HasTypeDescPi.piIntro LevelExpr.lzero.lsucc.lsucc LevelExpr.lzero.lsucc.lsucc flag
      ?innerDomainTyped ?innerCodomainTyped ?innerBodyTyped
    · exact HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation _ LevelExpr.lzero.lsucc flag)
    · exact HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation _ LevelExpr.lzero.lsucc flag)
    · exact HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation _ LevelExpr.lzero flag)

def metatheoryFuzzLambdaFamily : Nat → RawTerm 0
  | n => appCell (lamCell (lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)))
      (metatheoryFuzzFamily n)

theorem metatheoryFuzzLambdaFamily_typed {profile : PolyProfile} (n : Nat) :
    HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
      (metatheoryFuzzLambdaFamily n)
      (piTyCodeCell (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard)
        (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard)) :=
  HasTypeDescPi.piElim (nestedConstantLambdaTyping UniverseFlag.standard)
    (metatheoryFuzzFamily_typed n)

theorem metatheoryFuzzLambdaFamily_betaStep (n : Nat) :
    Step (metatheoryFuzzLambdaFamily n)
      (lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)) :=
  Step.beta

theorem metatheoryFuzzLambdaFamily_reducesToLambdaValue (n : Nat) :
    StepStar (metatheoryFuzzLambdaFamily n)
      (lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)) :=
  StepStar.single (metatheoryFuzzLambdaFamily_betaStep n)

/-- ★ The λ-value family normalizes to the constant lambda `λy.Type@0` — a FUNCTION value, not a type code. -/
theorem metatheoryFuzzLambdaFamily_normalizesToLambda {profile : PolyProfile} (n : Nat) :
    (metatheoryFuzzLambdaFamily_typed (profile := profile) n).normalForm
      = lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard) :=
  ((metatheoryFuzzLambdaFamily_typed (profile := profile) n).reachedNormalForm_eq_normalForm
    (metatheoryFuzzLambdaFamily_reducesToLambdaValue n) (by decide)).symm

/-- ★ Every λ-value family member EVALUATES TO A FUNCTION — its normal form is a λ (the Π-typed
canonical-forms branch the universe-code fuzz families never exercise). -/
theorem metatheoryFuzzLambdaFamily_evaluatesToFunction {profile : PolyProfile} (n : Nat) :
    ∃ body, (metatheoryFuzzLambdaFamily_typed (profile := profile) n).normalForm = lamCell body :=
  ⟨universeCodeCell LevelExpr.lzero UniverseFlag.standard,
    metatheoryFuzzLambdaFamily_normalizesToLambda n⟩

/-- Progress AT THE FUNCTION TYPE (firing-112 closedFunctionStepsOrIsLambda): each member steps or is a λ. -/
theorem metatheoryFuzzLambdaFamily_progress {profile : PolyProfile} (n : Nat) :
    (∃ reduct : RawTerm 0, Step (metatheoryFuzzLambdaFamily n) reduct)
    ∨ (∃ body : RawTerm 1, metatheoryFuzzLambdaFamily n = lamCell body) :=
  HasTypeDescPi.closedFunctionStepsOrIsLambda (metatheoryFuzzLambdaFamily_typed (profile := profile) n)

theorem metatheoryFuzzLambdaFamily_stronglyNormalizing {profile : PolyProfile} (n : Nat) :
    StepStar.IsStronglyNormalizing (metatheoryFuzzLambdaFamily n) :=
  HasTypeDescPi.stronglyNormalizingOfWfContextDesc WfContextDesc.emptyIsWellFormed
    (metatheoryFuzzLambdaFamily_typed (profile := profile) n)

end FX1Poly.Typed

#print axioms FX1Poly.Typed.metatheoryFuzzLambdaFamily_normalizesToLambda
#print axioms FX1Poly.Typed.metatheoryFuzzLambdaFamily_evaluatesToFunction
#print axioms FX1Poly.Typed.metatheoryFuzzLambdaFamily_progress
#print axioms FX1Poly.Typed.metatheoryFuzzLambdaFamily_stronglyNormalizing
