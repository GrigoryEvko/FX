import FX1Poly.Typed.HasTypeDescPiFundamentalVectorFromFormation

/-! # ScratchFT/HasTypeDescFundamentalVector
    — prototype of the formation-engine vector fundamental theorem
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

abbrev IsDescTelescopeReducibleAtVector {profile : PolyProfile} {baseScope currentDepth : Nat}
    {binderShifts : List Nat}
    (context : TypingContext profile (baseScope + currentDepth)) (levelsList : List LevelExpr)
    (flag : UniverseFlag) (children : RawTermChildren binderShifts baseScope)
    (_telescope : DescTelescope profile context levelsList flag children) : Prop :=
  ∀ {targetScope : Nat} (substitution : RawTermSubst (baseScope + currentDepth) (targetScope + 1))
    {envLevels : Fin (baseScope + currentDepth) → Nat} (_predLevel : Nat)
    (_env : ReducibleEnvVec envLevels context substitution)
    (shapeEq : binderShifts = consecutiveShifts currentDepth levelsList.length),
    TelescopeReducible flag currentDepth levelsList.length substitution levelsList (shapeEq ▸ children)

theorem HasTypeDesc.fundamentalVector {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeDesc profile context subject classifier) :
    IsFundamentalConclusionAtVector context subject classifier := by
  refine HasTypeDesc.rec
    (motive_1 := fun context subject classifier _typed =>
      IsFundamentalConclusionAtVector context subject classifier)
    (motive_2 := IsDescTelescopeReducibleAtVector)
    ?varArm ?convArm ?universeArm ?genFormationArm ?nilTelescope ?consTelescope typed
  · intro _scope context index
    intro _targetScope substitution _envLevels predLevel env
    exact env.lookupReducible index
  · intro _scope _context _subject _classifier _reclassifier levelExpr flag _typed converts
      _reclassifierTyped subjectFundamental reclassifierFundamental
    intro _targetScope substitution _envLevels predLevel env
    have reclassifierMember := reclassifierFundamental substitution (predLevel + 1) env
    rw [subst_universeCodeCell] at reclassifierMember
    obtain ⟨_candidate, reclassifierReducible⟩ := reclassifierMember.tarskiDecode
    exact IsReducibleMemberAt.castAlongConvUnderSubst substitution
      (subjectFundamental substitution predLevel env) reclassifierReducible converts
  · intro _scope _context levelExpr flag
    intro _targetScope _substitution _envLevels predLevel _env
    rw [subst_universeCodeCell, subst_universeCodeCell]
    exact IsReducibleMemberAt.universeFormation predLevel levelExpr flag
  · intro _scope _context generator _payload children levelsList flag rule isFormation premises
      premisesFundamental
    intro _targetScope substitution _envLevels predLevel env
    by_cases isPiFormer : generator = .gen_piTyCode
    · subst isPiFormer
      obtain rfl : rule = { outputType := universeFormerOutput } := Option.some.inj isFormation.symm
      match children with
      | .childCons _domainCode (.childCons _codomainCode .childNil) =>
          obtain ⟨_domainLevel, _codomainLevel, levelsShape⟩ := DescTelescope.twoChildLevels premises
          subst levelsShape
          dsimp only [universeFormerOutput]
          rw [subst_universeCodeCell]
          exact (FormerChildrenReducible.ofTelescopeReducible predLevel
            (premisesFundamental substitution predLevel env
              Generator.gen_piTyCode_binderShifts_eq)).toPiMember
    · by_cases isSigmaFormer : generator = .gen_sigmaTyCode
      · subst isSigmaFormer
        obtain rfl : rule = { outputType := universeFormerOutput } := Option.some.inj isFormation.symm
        match children with
        | .childCons _domainCode (.childCons _codomainCode .childNil) =>
            obtain ⟨_domainLevel, _codomainLevel, levelsShape⟩ := DescTelescope.twoChildLevels premises
            subst levelsShape
            dsimp only [universeFormerOutput]
            rw [subst_universeCodeCell]
            exact (FormerChildrenReducible.ofTelescopeReducible predLevel
              (premisesFundamental substitution predLevel env
                Generator.gen_sigmaTyCode_binderShifts_eq)).toSigmaMember
      · exfalso
        unfold typingRuleDescOf at isFormation
        rw [if_neg isPiFormer, if_neg isSigmaFormer] at isFormation
        contradiction
  · intro _baseScope _currentDepth _context _flag
    intro _targetScope _substitution _envLevels _predLevel _env _shapeEq
    exact True.intro
  · intro _baseScope _currentDepth _restShifts _context _head _headLevel _restLevels _flag _rest
      _headTyped _restTyped headFundamental restFundamental
    intro _targetScope substitution _envLevels predLevel env shapeEq
    simp only [List.length_cons, consecutiveShifts] at shapeEq
    obtain ⟨_headShiftEq, restShapeEq⟩ := List.cons.inj shapeEq
    subst restShapeEq
    refine ⟨fun level => ?_, fun {_memberLevel} argument argumentMember => ?_⟩
    · have headMember := headFundamental substitution level env
      rwa [subst_universeCodeCell] at headMember
    · exact restFundamental (RawTermSubst.cons argument substitution) predLevel
        (ReducibleEnvVec.cons env argumentMember) rfl

end FX1Poly.Typed
