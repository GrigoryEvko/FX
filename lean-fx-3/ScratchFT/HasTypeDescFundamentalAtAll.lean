import FX1Poly.Typed.FundamentalAtAllLeafArms
import FX1Poly.Typed.FundamentalAtAllTelescope
import FX1Poly.Typed.DescTelescopeInversion

/-! # ScratchFT/HasTypeDescFundamentalAtAll
    — prototype of the formation-fragment fundamental theorem over the all-level environment

This scratch file is not imported by the library.  It is the testbed for the `HasTypeDesc.fundamental`
piece that fills the `HasTypeDescPi.ofFormation` arm.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

abbrev DescTelescopeMotiveAtAll {profile : PolyProfile} {baseScope currentDepth : Nat}
    {binderShifts : List Nat}
    (context : TypingContext profile (baseScope + currentDepth)) (levels : List LevelExpr)
    (flag : UniverseFlag) (children : RawTermChildren binderShifts baseScope)
    (_telescope : DescTelescope profile context levels flag children) : Prop :=
  ∀ {targetScope : Nat} (substitution : RawTermSubst (baseScope + currentDepth) (targetScope + 1))
    (env : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat)
    (shapeEq : binderShifts = consecutiveShifts currentDepth levels.length),
    TelescopeReducible flag currentDepth levels.length substitution levels (shapeEq ▸ children)

theorem HasTypeDesc.fundamentalAtAll {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeDesc profile context subject classifier) :
    FundamentalConclusionAtAll context subject classifier := by
  refine HasTypeDesc.rec (motive_1 := fun context subject classifier typed =>
      FundamentalConclusionAtAll context subject classifier)
    (motive_2 := DescTelescopeMotiveAtAll)
    ?varArm ?convArm ?universeArm ?genFormationArm ?nilArm ?consArm typed
  · intro scope context index
    exact fundamentalVarAtAll context index
  · intro scope context subject classifier reclassifier levelExpr flag typed converts reclassifierTyped
      subjectFundamental reclassifierFundamental
    exact fundamentalConvAtAll subjectFundamental reclassifierFundamental converts
  · intro scope context levelExpr flag
    exact fundamentalUniverseFormationAtAll context levelExpr flag
  · intro scope context generator payload children levels flag rule isFormation premises premisesFundamental
    intro targetScope substitution env predLevel
    by_cases isPiFormer : generator = .gen_piTyCode
    · subst isPiFormer
      obtain rfl : rule = { outputType := universeFormerOutput } := Option.some.inj isFormation.symm
      match children with
      | .childCons domainCode (.childCons codomainCode .childNil) =>
          obtain ⟨domainLevel, codomainLevel, levelsShape⟩ := DescTelescope.twoChildLevels premises
          subst levelsShape
          dsimp only [universeFormerOutput]
          rw [subst_universeCodeCell]
          exact (FormerChildrenReducible.ofTelescopeReducible predLevel
            (premisesFundamental substitution env predLevel Generator.gen_piTyCode_binderShifts_eq)).toPiMember
    · by_cases isSigmaFormer : generator = .gen_sigmaTyCode
      · subst isSigmaFormer
        obtain rfl : rule = { outputType := universeFormerOutput } := Option.some.inj isFormation.symm
        match children with
        | .childCons domainCode (.childCons codomainCode .childNil) =>
            obtain ⟨domainLevel, codomainLevel, levelsShape⟩ := DescTelescope.twoChildLevels premises
            subst levelsShape
            dsimp only [universeFormerOutput]
            rw [subst_universeCodeCell]
            exact (FormerChildrenReducible.ofTelescopeReducible predLevel
              (premisesFundamental substitution env predLevel
                Generator.gen_sigmaTyCode_binderShifts_eq)).toSigmaMember
      · exfalso
        unfold typingRuleDescOf at isFormation
        rw [if_neg isPiFormer, if_neg isSigmaFormer] at isFormation
        contradiction
  · intro baseScope currentDepth context flag
    intro targetScope substitution env predLevel shapeEq
    exact fundamentalTelescopeNilAtAll
  · intro baseScope currentDepth restShifts context head headLevel restLevels flag rest headTyped restTyped
      headFundamental restFundamental
    intro targetScope substitution env predLevel shapeEq
    simp only [List.length_cons, consecutiveShifts] at shapeEq
    obtain ⟨_headShiftEq, restShapeEq⟩ := List.cons.inj shapeEq
    subst restShapeEq
    refine fundamentalTelescopeConsAtAll env headFundamental ?_
    intro memberLevel argument argumentMember
    -- This is the key experiment: the direct all-level telescope wants an all-level env for the tail,
    -- while the telescope relation supplies the head argument at one member level.
    sorry

end FX1Poly.Typed
