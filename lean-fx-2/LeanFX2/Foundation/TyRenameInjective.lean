import LeanFX2.Foundation.Ty
import LeanFX2.Foundation.RawTermInjective

/-! # Foundation/TyRenameInjective

Type-level rename injectivity under an injective raw renaming.

This is the type-index prerequisite for typed `Term.rename` injectivity:
hidden constructor parameters in `Term` include `Ty` payloads, so the typed
proof needs the same injective-renaming cancellation principle that raw terms
already have.
-/

namespace LeanFX2

theorem Ty.rename_injective_under_injective_renaming
    {level sourceScope : Nat} (sourceType : Ty level sourceScope) :
    ∀ {targetScope : Nat} {rho : RawRenaming sourceScope targetScope},
      RawRenamingInjective rho →
      ∀ (otherType : Ty level sourceScope),
        sourceType.rename rho = otherType.rename rho → sourceType = otherType := by
  induction sourceType with
  | unit =>
      intro _ _ _ otherType renameEq
      cases otherType <;> simp only [Ty.rename] at renameEq
      any_goals exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      rfl
  | bool =>
      intro _ _ _ otherType renameEq
      cases otherType <;> simp only [Ty.rename] at renameEq
      any_goals exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      rfl
  | nat =>
      intro _ _ _ otherType renameEq
      cases otherType <;> simp only [Ty.rename] at renameEq
      any_goals exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      rfl
  | arrow domainA codomainA domainIH codomainIH =>
      intro _ _ rhoInjective otherType renameEq
      cases otherType <;> simp only [Ty.rename] at renameEq
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · rename_i domainB codomainB
        injection renameEq with _ domainEq codomainEq
        rw [domainIH rhoInjective _ domainEq,
          codomainIH rhoInjective _ codomainEq]
      any_goals exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
  | piTy domainA codomainA domainIH codomainIH =>
      intro _ _ rhoInjective otherType renameEq
      cases otherType <;> simp only [Ty.rename] at renameEq
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · rename_i domainB codomainB
        injection renameEq with _ domainEq codomainEq
        rw [domainIH rhoInjective _ domainEq,
          codomainIH (RawRenamingInjective.lift rhoInjective) _ codomainEq]
      any_goals exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
  | sigmaTy firstA secondA firstIH secondIH =>
      intro _ _ rhoInjective otherType renameEq
      cases otherType <;> simp only [Ty.rename] at renameEq
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · rename_i firstB secondB
        injection renameEq with _ firstEq secondEq
        rw [firstIH rhoInjective _ firstEq,
          secondIH (RawRenamingInjective.lift rhoInjective) _ secondEq]
      any_goals exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
  | tyVar positionA =>
      intro _ _ rhoInjective otherType renameEq
      cases otherType <;> simp only [Ty.rename] at renameEq
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · rename_i positionB
        injection renameEq with _ positionEq
        exact congrArg Ty.tyVar (rhoInjective positionA positionB positionEq)
      any_goals exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
  | id carrierA leftA rightA carrierIH =>
      intro _ _ rhoInjective otherType renameEq
      cases otherType <;> simp only [Ty.rename] at renameEq
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · rename_i carrierB leftB rightB
        injection renameEq with _ carrierEq leftEq rightEq
        rw [carrierIH rhoInjective _ carrierEq,
          RawTerm.rename_injective_under_injective_renaming leftA
            rhoInjective leftB leftEq,
          RawTerm.rename_injective_under_injective_renaming rightA
            rhoInjective rightB rightEq]
      any_goals exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
  | listType elementA elementIH =>
      intro _ _ rhoInjective otherType renameEq
      cases otherType <;> simp only [Ty.rename] at renameEq
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · rename_i elementB
        injection renameEq with _ elementEq
        rw [elementIH rhoInjective _ elementEq]
      any_goals exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
  | optionType elementA elementIH =>
      intro _ _ rhoInjective otherType renameEq
      cases otherType <;> simp only [Ty.rename] at renameEq
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · rename_i elementB
        injection renameEq with _ elementEq
        rw [elementIH rhoInjective _ elementEq]
      any_goals exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
  | eitherType leftA rightA leftIH rightIH =>
      intro _ _ rhoInjective otherType renameEq
      cases otherType <;> simp only [Ty.rename] at renameEq
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · rename_i leftB rightB
        injection renameEq with _ leftEq rightEq
        rw [leftIH rhoInjective _ leftEq, rightIH rhoInjective _ rightEq]
      any_goals exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
  | «universe» universeLevelA levelLeA =>
      intro _ _ _ otherType renameEq
      cases otherType <;> simp only [Ty.rename] at renameEq
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · injection renameEq with _ universeLevelEq
        cases universeLevelEq
        congr
      any_goals exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
  | empty =>
      intro _ _ _ otherType renameEq
      cases otherType <;> simp only [Ty.rename] at renameEq
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · rfl
      any_goals exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
  | interval =>
      intro _ _ _ otherType renameEq
      cases otherType <;> simp only [Ty.rename] at renameEq
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · rfl
      any_goals exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
  | path carrierA leftA rightA carrierIH =>
      intro _ _ rhoInjective otherType renameEq
      cases otherType <;> simp only [Ty.rename] at renameEq
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      · rename_i carrierB leftB rightB
        injection renameEq with _ carrierEq leftEq rightEq
        rw [carrierIH rhoInjective _ carrierEq,
          RawTerm.rename_injective_under_injective_renaming leftA
            rhoInjective leftB leftEq,
          RawTerm.rename_injective_under_injective_renaming rightA
            rhoInjective rightB rightEq]
      any_goals exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
  | glue baseA boundaryA baseIH =>
      intro _ _ rhoInjective otherType renameEq
      cases otherType <;> simp only [Ty.rename] at renameEq
      any_goals exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      rename_i baseB boundaryB
      injection renameEq with _ baseEq boundaryEq
      rw [baseIH rhoInjective _ baseEq,
        RawTerm.rename_injective_under_injective_renaming boundaryA
          rhoInjective boundaryB boundaryEq]
  | oeq carrierA leftA rightA carrierIH =>
      intro _ _ rhoInjective otherType renameEq
      cases otherType <;> simp only [Ty.rename] at renameEq
      any_goals exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      rename_i carrierB leftB rightB
      injection renameEq with _ carrierEq leftEq rightEq
      rw [carrierIH rhoInjective _ carrierEq,
        RawTerm.rename_injective_under_injective_renaming leftA
          rhoInjective leftB leftEq,
        RawTerm.rename_injective_under_injective_renaming rightA
          rhoInjective rightB rightEq]
  | idStrict carrierA leftA rightA carrierIH =>
      intro _ _ rhoInjective otherType renameEq
      cases otherType <;> simp only [Ty.rename] at renameEq
      any_goals exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      rename_i carrierB leftB rightB
      injection renameEq with _ carrierEq leftEq rightEq
      rw [carrierIH rhoInjective _ carrierEq,
        RawTerm.rename_injective_under_injective_renaming leftA
          rhoInjective leftB leftEq,
        RawTerm.rename_injective_under_injective_renaming rightA
          rhoInjective rightB rightEq]
  | equiv domainA codomainA domainIH codomainIH =>
      intro _ _ rhoInjective otherType renameEq
      cases otherType <;> simp only [Ty.rename] at renameEq
      any_goals exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      rename_i domainB codomainB
      injection renameEq with _ domainEq codomainEq
      rw [domainIH rhoInjective _ domainEq,
        codomainIH rhoInjective _ codomainEq]
  | refine baseA predicateA baseIH =>
      intro _ _ rhoInjective otherType renameEq
      cases otherType <;> simp only [Ty.rename] at renameEq
      any_goals exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      rename_i baseB predicateB
      injection renameEq with _ baseEq predicateEq
      rw [baseIH rhoInjective _ baseEq,
        RawTerm.rename_injective_under_injective_renaming predicateA
          (RawRenamingInjective.lift rhoInjective) predicateB predicateEq]
  | record singleFieldA singleFieldIH =>
      intro _ _ rhoInjective otherType renameEq
      cases otherType <;> simp only [Ty.rename] at renameEq
      any_goals exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      rename_i singleFieldB
      injection renameEq with _ singleFieldEq
      rw [singleFieldIH rhoInjective _ singleFieldEq]
  | codata stateA outputA stateIH outputIH =>
      intro _ _ rhoInjective otherType renameEq
      cases otherType <;> simp only [Ty.rename] at renameEq
      any_goals exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      rename_i stateB outputB
      injection renameEq with _ stateEq outputEq
      rw [stateIH rhoInjective _ stateEq, outputIH rhoInjective _ outputEq]
  | session protocolA =>
      intro _ _ rhoInjective otherType renameEq
      cases otherType <;> simp only [Ty.rename] at renameEq
      any_goals exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      rename_i protocolB
      injection renameEq with _ protocolEq
      rw [RawTerm.rename_injective_under_injective_renaming protocolA
        rhoInjective protocolB protocolEq]
  | effect carrierA effectA carrierIH =>
      intro _ _ rhoInjective otherType renameEq
      cases otherType <;> simp only [Ty.rename] at renameEq
      any_goals exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      rename_i carrierB effectB
      injection renameEq with _ carrierEq effectEq
      rw [carrierIH rhoInjective _ carrierEq,
        RawTerm.rename_injective_under_injective_renaming effectA
          rhoInjective effectB effectEq]
  | modal modalityTagA carrierA carrierIH =>
      intro _ _ rhoInjective otherType renameEq
      cases otherType <;> simp only [Ty.rename] at renameEq
      any_goals exact Ty.noConfusion rfl rfl (heq_of_eq renameEq)
      rename_i modalityTagB carrierB
      injection renameEq with _ tagEq carrierEq
      rw [tagEq, carrierIH rhoInjective _ carrierEq]

end LeanFX2
