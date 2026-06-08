import FX1Poly.Typed.MetatheoryFuzz
import FX1Poly.Typed.GrownCanonicalFormsByClassifier

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

/-- `λx.λy.Type@0 : Π(Type@1, Π(Type@1, Type@1))` — a function returning the constant lambda. -/
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

/-- The λ-VALUE fuzz family: apply the nested constant function to the identity tower; each member
β-reduces to the constant lambda `λy.Type@0` — a FUNCTION value, not a type code. -/
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

end FX1Poly.Typed

#print axioms FX1Poly.Typed.nestedConstantLambdaTyping
#print axioms FX1Poly.Typed.metatheoryFuzzLambdaFamily_typed
#print axioms FX1Poly.Typed.metatheoryFuzzLambdaFamily_betaStep
