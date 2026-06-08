import FX1Poly.Typed.UniverseCodeConversion
import FX1Poly.Core.ReducibleTypeForwardClosure
import FX1Poly.Core.StrongNormalizationLeaves

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

theorem piTyCodeCell_not_conv_universeCodeCell {scope : Nat}
    {domain : RawTerm scope} {codomain : RawTerm (scope + 1)}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    ¬ Conv (piTyCodeCell domain codomain : RawTerm scope) (universeCodeCell levelExpr flag) := by
  intro conv
  obtain ⟨commonTerm, piReducesToCommon, universeReducesToCommon⟩ := conv
  have commonIsUniverse : commonTerm = universeCodeCell levelExpr flag :=
    StepStar.eq_of_noStep (fun _reduct step => noStep_universeCode (levelExpr, flag) step)
      universeReducesToCommon
  subst commonIsUniverse
  obtain ⟨_updatedDomain, _updatedCodomain, targetEq, _, _⟩ :=
    StepStar.piTyCode_decompose piReducesToCommon
  have headEq := congrArg RawTerm.headGenerator targetEq
  rw [headGenerator_universeCodeCell] at headEq
  change Generator.gen_universeCode = Generator.gen_piTyCode at headEq
  exact absurd headEq (by decide)

end FX1Poly.Typed

#print axioms FX1Poly.Typed.piTyCodeCell_not_conv_universeCodeCell
